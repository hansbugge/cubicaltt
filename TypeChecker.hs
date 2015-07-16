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
  TEnv { names   :: [String]  -- generated names
       , indent  :: Int
       , env     :: Env
       , verbose :: Bool  -- Should it be verbose and print what it typechecks?
       } deriving (Eq)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv [] 0 empty True
silentEnv  = TEnv [] 0 empty False

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
addTypeVal (x,a) (TEnv ns ind rho v) =
  let w@(VVar n _) = mkVarNice ns x a
  in TEnv (n:ns) ind (upd (x,w) rho) v

addSub :: (Name,Formula) -> TEnv -> TEnv
addSub iphi (TEnv ns ind rho v) = TEnv ns ind (sub iphi rho) v

addSubs :: [(Name,Formula)] -> TEnv -> TEnv
addSubs = flip $ foldr addSub

addType :: (Ident,Ter) -> TEnv -> TEnv
addType (x,a) tenv@(TEnv _ _ rho _) = addTypeVal (x,eval rho a) tenv

addBranch :: [(Ident,Val)] -> Env -> TEnv -> TEnv
addBranch nvs env (TEnv ns ind rho v) =
  TEnv ([n | (_,VVar n _) <- nvs] ++ ns) ind (upds nvs rho) v

addDecls :: [Decl] -> TEnv -> TEnv
addDecls d (TEnv ns ind rho v) = TEnv ns ind (def d rho) v

addDelDecls :: VDelSubst -> TEnv -> TEnv
addDelDecls d (TEnv ns ind rho v) = TEnv ns ind (delDef d rho) v

addTele :: Tele -> TEnv -> TEnv
addTele xas lenv = foldl (flip addType) lenv xas

faceEnv :: Face -> TEnv -> TEnv
faceEnv alpha tenv = tenv{env=env tenv `face` alpha}

-------------------------------------------------------------------------------
-- | Various useful functions

-- Extract the type of a label as a closure
getLblType :: LIdent -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ _ cas) r) = case lookupLabel c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType: " ++ show c ++ " in " ++ show cas)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Monadic version of unless
unlessM :: Monad m => m Bool -> m () -> m ()
unlessM mb x = mb >>= flip unless x

-- Constant path: <_> v
constPath :: Val -> Val
constPath = VPath (Name "_")

mkVars :: [String] -> Tele -> Env -> [(Ident,Val)]
mkVars _ [] _           = []
mkVars ns ((x,a):xas) nu =
  let w@(VVar n _) = mkVarNice ns x (eval nu a)
  in (x,w) : mkVars (n:ns) xas (upd (x,w) nu)

-- Construct a fuction "(_ : va) -> vb"
mkFun :: Val -> Val -> Val
mkFun va vb = VPi va (eval rho (Lam "_" (Var "a") (Var "b")))
  where rho = upd ("b",vb) (upd ("a",va) empty)

-- Construct "(x : b) -> IdP (<_> b) (f (g x)) x"
mkSection :: Val -> Val -> Val -> Val
mkSection vb vf vg =
  VPi vb (eval rho (Lam "x" b (IdP (Path (Name "_") b) (App f (App g x)) x)))
  where [b,x,f,g] = map Var ["b","x","f","g"]
        rho = upd ("g",vg) (upd ("f",vf) (upd ("b",vb) empty))

-- Test if two values are convertible
(===) :: Convertible a => a -> a -> Typing Bool
u === v = conv <$> asks names <*> pure u <*> pure v

-- eval in the typing monad
evalTyping :: Ter -> Typing Val
evalTyping t = eval <$> asks env <*> pure t

evalDelTyping :: Ter -> Typing Val
evalDelTyping t = evalDel <$> asks env <*> pure t

evalTypingDelSubst :: DelSubst -> Typing VDelSubst
evalTypingDelSubst t = evalDelSubst <$> asks env <*> pure t


-------------------------------------------------------------------------------
-- | The bidirectional type checker

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
  (VPi a f,Lam x a' t)  -> do
    check VU a'
    ns <- asks names
    rho <- asks env
    unlessM (a === eval rho a') $
      throwError "check: lam types don't match"
    let var = mkVarNice ns x a
    local (addTypeVal (x,a)) $ check (app todo f var) t
  (VSigma a f, Pair t1 t2) -> do
    check a t1
    v <- evalTyping t1
    check (app todo f v) t2
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
      throwError $ "path endpoints don't match for " ++ show e ++ ", got " ++
                   show (u0,u1) ++ ", but expected " ++ show (a0,a1)
  (VU,Glue a ts) -> do
    check VU a
    rho <- asks env
    checkGlue (eval rho a) ts
  (VGlue va ts,GlueElem u us) -> do
    check va u
    vu <- evalTyping u
    checkGlueElem vu ts us
  (VU,GlueLine b phi psi) -> do
    check VU b
    checkFormula phi
    checkFormula psi
  (VGlueLine vb phi psi,GlueLineElem r phi' psi') -> do
    check vb r
    unlessM ((phi,psi) === (phi',psi')) $
      throwError "GlueLineElem: formulas don't match"
  (VU, Later xi a) -> do
    _g' <- checkDelSubst xi
    vxi <- evalTypingDelSubst xi
    local (addDelDecls vxi) $ check VU a
  -- (VLater a rho, Next xi t) -> do
  --   g' <- checkDelSubst xi
  --   vxi <- evalTypingDelSubst xi
  --   unlessM (getDelValsE rho === getDelValsD vxi) $  -- compares them as finite maps, comparing names too
  --     throwError $ "delayed substitutions don't match: \n"
  --       ++ show (getDelValsE rho) ++ "\n/=\n" ++ show (getDelValsD vxi)
  --   let va = eval rho a
  --   local (\ rho' -> foldr addTypeVal rho' g') $ check va t  -- correct?
  (VLater va, Next xi t) -> do
    _g' <- checkDelSubst xi
    vxi <- evalTypingDelSubst xi
--    let va = eval rho a
    unlessM (getDelValsV va === getDelValsD vxi) $
      throwError $ "delayed substitutions don't match: \n"
        ++ show (getDelValsV va) ++ "\n/=\n" ++ show (getDelValsD vxi)
    local (addDelDecls vxi) $ check va t -- correct?
  _ -> do
    v <- infer t
    unlessM (v === a) $
      throwError $ "check conv:\n" ++ "inferred: " ++ show v ++ "\n/=\n" ++ "expected: " ++ show a

getDelValsV :: Val -> Map Ident Val
getDelValsV (Ter _ rho) = getDelValsE rho
getDelValsV (VPi v u) = getDelValsV v `Map.union` getDelValsV u
getDelValsV (VSigma v u) = getDelValsV v `Map.union` getDelValsV u
getDelValsV (VPair v u) = getDelValsV v `Map.union` getDelValsV u
-- TODO: finish this function
-- getDelValsV (VCon _ vs) = foldr Map.union (map getDelValsV vs) Map.empty
getDelValsV _ = Map.empty

getDelValsE :: Env -> Map Ident Val
getDelValsE (DelUpd f rho,vs,fs,w:ws) = Map.insert f w $ getDelValsE (rho,vs,fs,ws)
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
checkDelSubst :: DelSubst -> Typing [(Ident, Val)]
checkDelSubst [] = return []
checkDelSubst ((DelBind (f,(a,t))) : ds) = do
  g' <- checkDelSubst ds
  local (\ e -> foldr addTypeVal e g') $ check VU a
  vla <- evalTyping (Later ds a)
  va <- evalTyping a
  check vla t
  return ((f,va) : g')

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
    (throwError $ "Incompatible system " ++ show vus)

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
  checkSystemsWith ts us (\_ vt u -> check (hisoDom vt) u)
  let vus = evalSystem rho us
  checkSystemsWith ts vus (\alpha vt vAlpha ->
    unlessM (app todo (hisoFun vt) vAlpha === (vu `face` alpha)) $
      throwError $ "Image of glueElem component " ++ show vAlpha ++
                   " doesn't match " ++ show vu)
  checkCompSystem vus

checkGlue :: Val -> System Ter -> Typing ()
checkGlue va ts = do
  checkSystemWith ts (\alpha tAlpha -> checkIso (va `face` alpha) tAlpha)
  rho <- asks env
  checkCompSystem (evalSystem rho ts)

-- An iso for a type b is a five-tuple: (a,f,g,r,s)   where
--  a : U
--  f : a -> b
--  g : b -> a
--  s : forall (y : b), f (g y) = y
--  t : forall (x : a), g (f x) = x
checkIso :: Val -> Ter -> Typing ()
checkIso vb (Pair a (Pair f (Pair g (Pair s t)))) = do
  check VU a
  va <- evalTyping a
  check (mkFun va vb) f
  check (mkFun vb va) g
  vf <- evalTyping f
  vg <- evalTyping g
  check (mkSection vb vf vg) s
  check (mkSection va vg vf) t

checkBranch :: (Label,Env) -> Val -> Branch -> Val -> Val -> Typing ()
checkBranch (OLabel _ tele,nu) f (OBranch c ns e) _ _ = do
  ns' <- asks names
  let us = map snd $ mkVars ns' tele nu
  local (addBranch (zip ns us) nu) $ check (app todo f (VCon c us)) e
checkBranch (PLabel _ tele is ts,nu) f (PBranch c ns js e) g va = do
  ns' <- asks names
  -- mapM_ checkFresh js
  let us   = mkVars ns' tele nu
      vus  = map snd us
      js'  = map Atom js
      vts  = evalSystem (subs (zip is js') (upds us nu)) ts
      vgts = intersectionWith (app todo) (border g vts) vts
  local (addSubs (zip js js') . addBranch (zip ns vus) nu) $ do
    check (app todo f (VPCon c va vus js')) e
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
      (a0,a1)  <- checkPath (constPath (va `face` alpha)) pAlpha
      unlessM (a0 === eval rhoAlpha t0) $
        throwError $ "Incompatible system with " ++ show t0
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
  Var n     -> lookType n <$> asks env
  App t u -> do
    c <- infer t
    case c of
      VPi a f -> do
        check a u
        v <- evalTyping u
        return $ app todo f v
      _       -> throwError $ show c ++ " is not a product"
  Fix a t -> do
     check VU a
--     va <- evalDelTyping a
     va' <- evalDelTyping a
     rho <- asks env
     check (VPi (VLater va') (Ter (Lam "_fixTy" (Later [] a) a) rho)) t
     return va'
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
        return $ app todo f (fstVal v)
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
  Trans p t -> do
    (a0,a1) <- checkPath (constPath VU) p
    check a0 t
    return a1
  Comp a t0 ps -> do
    check VU a
    va <- evalTyping a
    check va t0
    checkPathSystem t0 va ps
    return va
  CompElem a es u us -> do
    check VU a
    rho <- asks env
    let va = eval rho a
    ts <- checkPathSystem a VU es
    let ves = evalSystem rho es
    unless (keys es == keys us)
      (throwError ("Keys don't match in " ++ show es ++ " and " ++ show us))
    check va u
    let vu = eval rho u
    checkSystemsWith ts us (const check)
    let vus = evalSystem rho us
    checkCompSystem vus
    checkSystemsWith ves vus (\alpha eA vuA ->
      unlessM (transNegLine eA vuA === (vu `face` alpha)) $
        throwError $ "Malformed compElem: " ++ show us)
    return $ compLine VU va ves
  ElimComp a es u -> do
    check VU a
    rho <- asks env
    let va = eval rho a
    checkPathSystem a VU es
    let ves = evalSystem rho es
    check (compLine VU va ves) u
    return va
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
