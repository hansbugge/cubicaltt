{-# LANGUAGE TupleSections #-}
module TypeChecker where

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey,elems,keys
                ,intersection,intersectionWith,intersectionWithKey
                ,toList,fromList)
import qualified Data.Map as Map
import qualified Data.Traversable as T

import Connections
import CTT
import Eval

-- Type checking monad
type Typing a = ReaderT TEnv (ExceptT String IO) a

-- Environment for type checker
data TEnv =
  TEnv { names   :: [String] -- generated names
       , indent  :: Int
       , env     :: Env
       , verbose :: Bool  -- Should it be verbose and print what it typechecks?
       , context :: !(Map Ident Val) -- typing context
       } deriving (Eq)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv [] 0 emptyEnv True Map.empty
silentEnv  = TEnv [] 0 emptyEnv False Map.empty

-- Trace function that depends on the verbosity flag
trace :: String -> Typing ()
trace s = do
  b <- asks verbose
  when b $ liftIO (putStrLn s)

-------------------------------------------------------------------------------
-- | Functions for running computations in the type checker monad

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runExceptT $ runReaderT t env

runDecls :: TEnv -> [Decl] -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  return $ addDecls d tenv

runDeclss :: TEnv -> [[Decl]] -> IO (Maybe String,TEnv)
runDeclss tenv []     = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (infer e)

-------------------------------------------------------------------------------
-- | Modifiers for the environment

addTypeVal :: (Ident,Val) -> TEnv -> TEnv
addTypeVal (x,a) (TEnv ns ind rho v c) =
  let w@(VVar n _) = mkVarNice ns x a
  in TEnv (n:ns) ind (upd (x,w) rho) v (Map.insert x a c)

addSub :: (Name,Formula) -> TEnv -> TEnv
addSub iphi (TEnv ns ind rho v c) = TEnv ns ind (sub iphi rho) v c

addSubs :: [(Name,Formula)] -> TEnv -> TEnv
addSubs = flip $ foldr addSub

addSubk :: (Clock,Clock) -> TEnv -> TEnv
addSubk kk (TEnv ns ind rho v c) = TEnv ns ind (subk kk rho) v c

addType :: (Ident,Ter) -> TEnv -> TEnv
addType (x,a) tenv = addTypeVal (x,eval (env tenv) a) tenv

addBranch :: [(Ident,Val)] -> Env -> TEnv -> TEnv
addBranch nvs env (TEnv ns ind rho v c) =
  TEnv ([n | (_,VVar n _) <- nvs] ++ ns) ind (upds nvs rho) v (Map.fromList [ (x,a) | (x,VVar n a) <- nvs ] `Map.union` c)

addDecls :: [Decl] -> TEnv -> TEnv
addDecls d (TEnv ns ind rho v c) = TEnv ns ind (def d rho) v (Map.fromList [ (x,eval (def d rho) a) | (x,(a,_)) <- d ] `Map.union` c)

addDelDecls :: Tag -> VDelSubst -> [(Ident,Val)] -> TEnv -> TEnv
addDelDecls t ds xas (TEnv ns ind rho v c) = TEnv ns ind rho' v (Map.fromList xas `Map.union` c)
  where rho' = pushDelSubst t ds rho

addTele :: Tele -> TEnv -> TEnv
addTele xas lenv = foldl (flip addType) lenv xas

faceEnv :: Face -> TEnv -> TEnv
faceEnv alpha tenv = tenv{env=env tenv `face` alpha, context = Map.map (`face` alpha) (context tenv)}

-------------------------------------------------------------------------------
-- | Various useful functions

-- Extract the type of a label as a closure
getLblType :: LIdent -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ _ cas) r) = case lookupLabel c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType: " ++ show c ++ " in " ++ show cas)
getLblType c (Ter (HSum _ _ cas) r) = case lookupLabel c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType: " ++ show c ++ " in " ++ show cas)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Monadic version of unless
unlessM :: Monad m => m Bool -> m () -> m ()
unlessM mb x = mb >>= flip unless x

mkVars :: [String] -> Tele -> Env -> [(Ident,Val)]
mkVars _ [] _           = []
mkVars ns ((x,a):xas) nu =
  let w@(VVar n _) = mkVarNice ns x (eval nu a)
  in (x,w) : mkVars (n:ns) xas (upd (x,w) nu)

-- Test if two values are convertible
(===) :: Convertible a => a -> a -> Typing Bool
u === v = conv <$> asks names <*> pure u <*> pure v

-- eval in the typing monad
evalTyping :: Ter -> Typing Val
evalTyping t = eval <$> asks env <*> pure t

evalTypingDelSubst :: Tag -> DelSubst -> Typing VDelSubst
evalTypingDelSubst l t = evalDelSubst l <$> asks env <*> pure t


-------------------------------------------------------------------------------
-- | The bidirectional type checker

forceT :: Val -> Val
forceT (Ter (Later _ k xi t) rho) = let l = fresht rho in VLater l (lookClock k rho) (eval (pushDelSubst l (evalDelSubst l rho xi) rho) t)
forceT v  = v

-- Check that t has type a
check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Undef{}) -> return ()
  (_,Hole l)  -> do
      rho <- asks env
      let e = unlines (reverse (contextOfEnv rho))
      ns <- asks names
      trace $ "\nHole at " ++ show l ++ ":\n\n" ++
              e ++ replicate 80 '-' ++ "\n" ++ show (normal ns a)  ++ "\n"
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi f)       -> checkFam f
  (VU,Sigma f)    -> checkFam f
  (VU,Sum _ _ bs) -> forM_ bs $ \lbl -> case lbl of
    OLabel _ tele -> checkTele tele
    PLabel _ tele is ts ->
      throwError $ "check: no path constructor allowed in " ++ show t
  (VU,HSum _ _ bs) -> forM_ bs $ \lbl -> case lbl of
    OLabel _ tele -> checkTele tele
    PLabel _ tele is ts -> do
      checkTele tele
      rho <- asks env
      unless (all (`elem` is) (domain ts)) $
        throwError "names in path label system" -- TODO
      mapM_ checkFresh is
      let iis = zip is (map Atom is)
      local (addSubs iis . addTele tele) $ do
        checkSystemWith ts $ \alpha talpha ->
          local (faceEnv alpha) $
            -- NB: the type doesn't depend on is
            check (Ter t rho) talpha
        rho' <- asks env
        checkCompSystem (evalSystem rho' ts)
  (VPi va@(Ter (Sum _ _ cas) nu) f,Split _ _ ty ces) -> do
    check VU ty
    rho <- asks env
    unlessM (a === eval rho ty) $ throwError "check: split annotations"
    if map labelName cas == map branchName ces
       then sequence_ [ checkBranch (lbl,nu) f brc (Ter t rho) va
                      | (brc, lbl) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi va@(Ter (HSum _ _ cas) nu) f,Split _ _ ty ces) -> do
    check VU ty
    rho <- asks env
    unlessM (a === eval rho ty) $ throwError "check: split annotations"
    if map labelName cas == map branchName ces
       then sequence_ [ checkBranch (lbl,nu) f brc (Ter t rho) va
                      | (brc, lbl) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x a' t)  -> do
    check VU a'
    ns <- asks names
    rho <- asks env
    unlessM (a === eval rho a') $
      throwError $ "check: lam types don't match"
        ++ "\nlambda type annotation: " ++ show a'
        ++ "\ndomain of Pi: " ++ show a
    let var = mkVarNice ns x a
    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, Pair t1 t2) -> do
    check a t1
    v <- evalTyping t1
    check (app f v) t2
  (_,Where e d) -> do
    local (\tenv@TEnv{indent=i} -> tenv{indent=i + 2}) $ checkDecls d
    local (addDecls d) $ check a e
  (VU,IdP a e0 e1) -> do
    (a0,a1) <- checkPath (constPath VU) a
    check a0 e0
    check a1 e1
  (VIdP p a0 a1,Path _ e) -> do
    (u0,u1) <- checkPath p t
    ns <- asks names
    unless (conv ns a0 u0 && conv ns a1 u1) $
      throwError $ concat $ ["path endpoints don't match for ", show e, ", got:\n  "
                            ,show u0,"\n  ",show u1, "\nexpected: \n  ", show a0,"\n  ",show a1,"\n"]
  (VU,Glue a ts) -> do
    check VU a
    rho <- asks env
    checkGlue (eval rho a) ts
  (VGlue va ts,GlueElem u us) -> do
    check va u
    vu <- evalTyping u
    checkGlueElem vu ts us
  (VU, Later _ k xi a) -> do
    rho <- asks env
    let l = fresht rho
--        k' = lookClock k rho
    g <- checkDelSubst l k xi
    vxi <- evalTypingDelSubst l xi
    local (addDelDecls l vxi g) $ check VU a
  (VU, Forall k a) -> do
    rho <- asks env
    local (addSubk (k,freshk rho)) $ check VU a
  (VForall k va, CLam kt t') -> do
    rho <- asks env
    let k' = freshk (va,rho)
    local (addSubk (kt,k')) $ check (act va (k,k')) t'
  (_, Next _ kt xi t' s) | VLater _ k va <- forceT a -> do
    rho <- asks env
    ns <- asks names
    let k' = lookClock kt rho
    unless (k == k') $
      throwError $ "clocks do not match:\n" ++ show a ++ " " ++ show t
    let l = fresht (rho,va)
    g <- checkDelSubst l kt xi
    vxi <- evalTypingDelSubst l xi
    local (addDelDecls l vxi g) $ check va t'
    checkSystemWith s (\ alpha b -> local (faceEnv alpha) $ check (a `face` alpha) b)
    checkSystemWith s (\ alpha b -> local (faceEnv alpha) $ do
      rho <- asks env
      let
          vb    = eval rho b
          v1    = eval (pushDelSubst l (bangS vxi)                     rho) t'
          v2    = eval (pushDelSubst l (bangS (singleton "x" vb)) emptyEnv) (Var "x")
      unless (conv ns v1 v2) $
        throwError $ concat ["check next: system does not align\n",show (normal ns v1),"\n\n",show (normal ns v2),"\n"
                            ] )
    checkCompSystem (evalSystem rho s)


  _ -> do
    v <- infer t
    unlessM (v === a) $
      throwError $ "check conv:\n" ++ "inferred: " ++ show v ++ "\n/=\n" ++ "expected: " ++ show a

bangS :: VDelSubst -> VDelSubst
bangS = fmap (fmap bang)

getDelValsV :: Val -> Map Ident Val
getDelValsV (Ter _ rho) = getDelValsE rho
getDelValsV (VPi v u) = getDelValsV v `Map.union` getDelValsV u
getDelValsV (VSigma v u) = getDelValsV v `Map.union` getDelValsV u
getDelValsV (VPair v u) = getDelValsV v `Map.union` getDelValsV u
-- TODO: finish this function
-- getDelValsV (VCon _ vs) = foldr Map.union (map getDelValsV vs) Map.empty
getDelValsV _ = Map.empty

getDelValsE :: Env -> Map Ident Val
--getDelValsE (DelUpd f rho,vs,fs,w:ws) = Map.insert f w $ getDelValsE (rho,vs,fs,ws)
getDelValsE (Upd _ rho,_:vs,fs,ws)    = getDelValsE (rho,vs,fs,ws)
getDelValsE (Def _ rho,vs,fs,ws)      = getDelValsE (rho,vs,fs,ws)
getDelValsE (Sub _ rho,vs,_:fs,ws)    = getDelValsE (rho,vs,fs,ws)
getDelValsE (Empty,_,_,_)             = Map.empty

getDelValsD :: VDelSubst -> Map Ident Val
getDelValsD ds = Map.fromList $ map (\ (DelBind (f,(a,v))) -> (f,v)) ds

-- getDelValsE :: Env -> [(Ident,Val)]
-- getDelValsE (DelUpd f rho,vs,fs,w:ws) = (f,w) : getDelValsE (rho,vs,fs,ws)
-- getDelValsE (Upd _ rho,_:vs,fs,ws)    = getDelValsE (rho,vs,fs,ws)
-- getDelValsE (Def _ rho,vs,fs,ws)      = getDelValsE (rho,vs,fs,ws)
-- getDelValsE (Sub _ rho,vs,_:fs,ws)    = getDelValsE (rho,vs,fs,ws)
-- getDelValsE (Empty,_,_,_)             = []

-- getDelValsD :: VDelSubst -> [(Ident,Val)]
-- getDelValsD = map (\ (DelBind (f,(a,v))) -> (f,v))

--(>==) :: [(Ident,Val)] -> [(Ident,Val)] -> Bool
--xs >== ys = ?

-- Check a delayed substitution
checkDelSubst :: Tag -> Clock -> DelSubst -> Typing [(Ident, Val)]
checkDelSubst l k []                         = return []
checkDelSubst l k ((DelBind (f,(a',t))) : ds) = do
  g <- checkDelSubst l k ds
  va <- case a' of
         Just a -> do
           local (\ e -> foldr addTypeVal e g) $ check VU a
           vds <- evalTypingDelSubst l ds
           va <- local (addDelDecls l vds g) $ evalTyping a
           rho <- asks env
           check (VLater l (lookClock k rho) va) t
           return va
         Nothing -> do
           vla <- infer t
           rho <- asks env
           case forceT vla of
             VLater l' k' w | lookClock k rho == k' -> return (w `act` (l',l))
             w -> throwError $ "checkDelSusbst: not the right later " ++ show w
  return ((f,va) : g)

-- Check a list of declarations
checkDecls :: [Decl] -> Typing ()
checkDecls d = do
  let (idents,tele,ters) = (declIdents d,declTele d,declTers d)
  ind <- asks indent
  trace (replicate ind ' ' ++ "Checking: " ++ unwords idents)
  checkTele tele
  local (addDecls d) $ do
    rho <- asks env
    checks (tele,rho) ters

-- Check a telescope
checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  local (addType (x,a)) $ checkTele xas

-- Check a family
checkFam :: Ter -> Typing ()
checkFam (Lam x a b) = do
  check VU a
  local (addType (x,a)) $ check VU b
checkFam x = throwError $ "checkFam: " ++ show x

-- Check that a system is compatible
checkCompSystem :: System Val -> Typing ()
checkCompSystem vus = do
  ns <- asks names
  unless (isCompSystem ns vus)
    (throwError $ "Incompatible system " ++ showSystem vus)

-- Check the values at corresponding faces with a function, assumes
-- systems have the same faces
checkSystemsWith :: System a -> System b -> (Face -> a -> b -> Typing c) ->
                    Typing ()
checkSystemsWith us vs f = sequence_ $ elems $ intersectionWithKey f us vs

-- Check the faces of a system
checkSystemWith :: System a -> (Face -> a -> Typing b) -> Typing ()
checkSystemWith us f = sequence_ $ elems $ mapWithKey f us

-- Check a glueElem
checkGlueElem :: Val -> System Val -> System Ter -> Typing ()
checkGlueElem vu ts us = do
  unless (keys ts == keys us)
    (throwError ("Keys don't match in " ++ show ts ++ " and " ++ show us))
  rho <- asks env
  checkSystemsWith ts us (\_ vt u -> check (isoDom vt) u)
  let vus = evalSystem rho us
  checkSystemsWith ts vus (\alpha vt vAlpha ->
    unlessM (app (isoFun vt) vAlpha === (vu `face` alpha)) $
      throwError $ "Image of glueElem component " ++ show vAlpha ++
                   " doesn't match " ++ show vu)
  checkCompSystem vus

checkGlue :: Val -> System Ter -> Typing ()
checkGlue va ts = do
  checkSystemWith ts (\alpha tAlpha -> checkIso (va `face` alpha) tAlpha)
  rho <- asks env
  checkCompSystem (evalSystem rho ts)

-- An iso for a type b is a five-tuple: (a,f,g,s,t)   where
--  a : U
--  f : a -> b
--  g : b -> a
--  s : forall (y : b), f (g y) = y
--  t : forall (x : a), g (f x) = x
mkIso :: Val -> Val
mkIso vb = eval rho $
  Sigma $ Lam "a" U $
  Sigma $ Lam "f" (Pi (Lam "_" a b)) $
  Sigma $ Lam "g" (Pi (Lam "_" b a)) $
  Sigma $ Lam "s" (Pi (Lam "y" b $ IdP (Path (Name "_") b) (App f (App g y)) y)) $
    Pi (Lam "x" a $ IdP (Path (Name "_") a) (App g (App f x)) x)
  where [a,b,f,g,x,y] = map Var ["a","b","f","g","x","y"]
        rho = upd ("b",vb) emptyEnv

checkIso :: Val -> Ter -> Typing ()
checkIso vb iso = check (mkIso vb) iso

checkBranch :: (Label,Env) -> Val -> Branch -> Val -> Val -> Typing ()
checkBranch (OLabel _ tele,nu) f (OBranch c ns e) _ _ = do
  ns' <- asks names
  let us = map snd $ mkVars ns' tele nu
  local (addBranch (zip ns us) nu) $ check (app f (VCon c us)) e
checkBranch (PLabel _ tele is ts,nu) f (PBranch c ns js e) g va = do
  ns' <- asks names
  -- mapM_ checkFresh js
  let us   = mkVars ns' tele nu
      vus  = map snd us
      js'  = map Atom js
      vts  = evalSystem (subs (zip is js') (upds us nu)) ts
      vgts = intersectionWith (app) (border g vts) vts
  local (addSubs (zip js js') . addBranch (zip ns vus) nu) $ do
    check (app f (VPCon c va vus js')) e
    ve  <- evalTyping e -- TODO: combine with next two lines?
    let veborder = border ve vts
    unlessM (veborder === vgts) $
      throwError $ "Faces in branch for " ++ show c ++ " don't match:"
                   ++ "\ngot\n" ++ showSystem veborder ++ "\nbut expected\n"
                   ++ showSystem vgts

checkFormula :: Formula -> Typing ()
checkFormula phi = do
  rho <- asks env
  let dom = domainEnv rho
  unless (all (`elem` dom) (support phi)) $
    throwError $ "checkFormula: " ++ show phi

checkFresh :: Name -> Typing ()
checkFresh i = do
  rho <- asks env
  when (i `elem` support rho)
    (throwError $ show i ++ " is already declared")

-- Check that a term is a path and output the source and target
checkPath :: Val -> Ter -> Typing (Val,Val)
checkPath v (Path i a) = do
  rho <- asks env
  -- checkFresh i
  local (addSub (i,Atom i)) $ check (v @@ i) a
  return (eval (sub (i,Dir 0) rho) a,eval (sub (i,Dir 1) rho) a)
checkPath v t = do
  vt <- infer t
  case vt of
    VIdP a a0 a1 -> do
      unlessM (a === v) $ throwError "checkPath"
      return (a0,a1)
    _ -> throwError $ show vt ++ " is not a path"

-- Return system such that:
--   rhoalpha |- p_alpha : Id (va alpha) (t0 rhoalpha) ualpha
-- Moreover, check that the system ps is compatible.
checkPathSystem :: Ter -> Val -> System Ter -> Typing (System Val)
checkPathSystem t0 va ps = do
  rho <- asks env
  v <- T.sequence $ mapWithKey (\alpha pAlpha ->
    local (faceEnv alpha) $ do
      rhoAlpha <- asks env
      (a0,a1)  <- checkPath (va `face` alpha) pAlpha
      unlessM (a0 === eval rhoAlpha t0) $
        throwError $ "Incompatible system " ++ showSystem ps ++
                     ", component\n " ++ show pAlpha ++
                     "\nincompatible  with\n " ++ show t0
      return a1) ps
  checkCompSystem (evalSystem rho ps)
  return v

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval nu a) e
  v' <- evalTyping e
  checks (xas,upd (x,v') nu) es
checks _              _      = throwError "checks"

-- infer the type of e
infer :: Ter -> Typing Val
infer e = case e of
  U         -> return VU  -- U : U
  Var n     -> (Map.! n) <$> asks context
  App t u -> do
    c <- infer t
    case c of
      VPi a f -> do
        check a u
        v <- evalTyping u
        return $ app f v
      _       -> throwError $ show c ++ " is not a product"
  DFix k a t -> do
    check VU a
    va <- evalTyping a
    rho <- asks env
    let l = fresht (rho,va)
        k' = lookClock k rho
    check (VPi (VLater l k' va) (Ter (Lam "_fixTy" (Later (Loc { locFile = "Typechecker" , locPos = (0,0)}) k [] a) a) rho)) t
    return (VLater l k' va)
  CApp t k -> do
    rho <- asks env
    let kv = lookClock k rho
    c <- infer t
    case c of
      VForall k' va -> return (actk va (k',kv))
      _             -> throwError $ show c ++ " is not a clock quantification"
  Prev k' t -> do
    rho <- asks env
    let k = freshk rho
    c <- local (addSubk (k',k)) $ infer t
    case forceT c of
       VLater l kl a | kl == k   -> return (VForall k (adv l k a))
                     | otherwise -> throwError $ show c ++ " does not match clock " ++ show k
       _                         -> throwError $ show c ++ " is not a |> type"
  Fst t -> do
    c <- infer t
    case c of
      VSigma a f -> return a
      _          -> throwError $ show c ++ " is not a sigma-type"
  Snd t -> do
    c <- infer t
    case c of
      VSigma a f -> do
        v <- evalTyping t
        return $ app f (fstVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    local (addDecls d) $ infer t
  AppFormula e phi -> do
    checkFormula phi
    t <- infer e
    case t of
      VIdP a _ _ -> return $ a @@ phi
      _ -> throwError (show e ++ " is not a path")
  Comp a t0 ps -> do
    (va0, va1) <- checkPath (constPath VU) a
    va <- evalTyping a
    check va0 t0
    checkPathSystem t0 va ps
    return va1
  Fill a t0 ps -> do
    (va0, va1) <- checkPath (constPath VU) a
    va <- evalTyping a
    check va0 t0
    checkPathSystem t0 va ps
    vt  <- evalTyping t0
    rho <- asks env
    let vps = evalSystem rho ps
    return (VIdP va vt (compLine va vt vps))
  PCon c a es phis -> do
    check VU a
    va <- evalTyping a
    (bs,nu) <- getLblType c va
    checks (bs,nu) es
    mapM_ checkFormula phis
    return va
  _ -> throwError ("infer " ++ show e)

-- Not used since we have U : U
--
-- (=?=) :: Typing Ter -> Ter -> Typing ()
-- m =?= s2 = do
--   s1 <- m
--   unless (s1 == s2) $ throwError (show s1 ++ " =/= " ++ show s2)
--
-- checkTs :: [(String,Ter)] -> Typing ()
-- checkTs [] = return ()
-- checkTs ((x,a):xas) = do
--   checkType a
--   local (addType (x,a)) (checkTs xas)
--
-- checkType :: Ter -> Typing ()
-- checkType t = case t of
--   U              -> return ()
--   Pi a (Lam x b) -> do
--     checkType a
--     local (addType (x,a)) (checkType b)
--   _ -> infer t =?= U
