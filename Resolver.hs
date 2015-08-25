{-# LANGUAGE TupleSections #-}

-- | Convert the concrete syntax into the syntax of cubical TT.
module Resolver where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import Data.List
import Data.Map (Map,(!))
import qualified Data.Map as Map

import Exp.Abs
import CTT (Ter,Ident,Loc(..),mkApps,mkWheres)
import qualified CTT
import Connections (negFormula,andFormula,orFormula)
import qualified Connections as C

-- | Useful auxiliary functions

-- Applicative cons
(<:>) :: Applicative f => f a -> f [a] -> f [a]
a <:> b = (:) <$> a <*> b

-- Un-something functions
unVar :: Exp -> Maybe Ident
unVar (Var (AIdent (_,x))) = Just x
unVar _                    = Nothing

unWhere :: ExpWhere -> Exp
unWhere (Where e ds) = Let ds e
unWhere (NoWhere e)  = e

-- Tail recursive form to transform a sequence of applications
-- App (App (App u v) ...) w  into (u, [v, …, w])
-- (cleaner than the previous version of unApps)
unApps :: Exp -> [Exp] -> (Exp, [Exp])
unApps (App u v) ws = unApps u (v : ws)
unApps u         ws = (u, ws)

-- Turns an expression of the form App (... (App id1 id2) ... idn)
-- into a list of idents
appsToIdents :: Exp -> Maybe [Ident]
appsToIdents = mapM unVar . uncurry (:) . flip unApps []

-- Transform a sequence of applications
-- (((u v1) .. vn) phi1) .. phim into (u,[v1,..,vn],[phi1,..,phim])
unAppsFormulas :: Exp -> [Formula]-> (Exp,[Exp],[Formula])
unAppsFormulas (AppFormula u phi) phis = unAppsFormulas u (phi:phis)
unAppsFormulas u phis = (x,xs,phis)
  where (x,xs) = unApps u []

-- Flatten a tele
flattenTele :: [Tele] -> [Either (Ident,Exp) Ident]
flattenTele tele = do
  t <- tele
  case t of
    Tele id ids typ -> do
          i <- id:ids
          return $ Left (unAIdent i,typ)
    CTele idk -> return (Right (unAIdent idk))

-- Flatten a PTele
flattenPTele :: [PTele] -> Resolver [(Ident,Exp)]
flattenPTele []                   = return []
flattenPTele (PTele exp typ : xs) = case appsToIdents exp of
  Just ids -> do
    pt <- flattenPTele xs
    return $ map (,typ) ids ++ pt
  Nothing -> throwError "malformed ptele"

-------------------------------------------------------------------------------
-- | Resolver and environment

data SymKind = Variable | Constructor | PConstructor | Name | Clock
  deriving (Eq,Show)

-- local environment for constructors
data Env = Env { envModule :: String,
                 variables :: [(Ident,SymKind)] }
  deriving (Eq,Show)

type Resolver a = ReaderT Env (ExceptT String Identity) a

emptyEnv :: Env
emptyEnv = Env "" []

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runExceptT $ runReaderT x emptyEnv

updateModule :: String -> Env -> Env
updateModule mod e = e{envModule = mod}

insertIdent :: (Ident,SymKind) -> Env -> Env
insertIdent (n,var) e
  | n == "_"  = e
  | otherwise = e{variables = (n,var) : variables e}

insertIdents :: [(Ident,SymKind)] -> Env -> Env
insertIdents = flip $ foldr insertIdent

insertClock :: AIdent -> Env -> Env
insertClock (AIdent (_,x)) | CTT.Clock x /= CTT.k0 = insertIdent (x,Clock)
insertClock (AIdent (_,x)) | otherwise             = error "not allowed to shadow k0"

insertClocks :: [AIdent] -> Env -> Env
insertClocks = flip $ foldr insertClock

insertName :: AIdent -> Env -> Env
insertName (AIdent (_,x)) = insertIdent (x,Name)

insertNames :: [AIdent] -> Env -> Env
insertNames = flip $ foldr insertName

insertVar :: Ident -> Env -> Env
insertVar x = insertIdent (x,Variable)

insertVars :: [Ident] -> Env -> Env
insertVars = flip $ foldr insertVar

insertTele :: [(Either (Ident,Exp) Ident)] -> Env -> Env
insertTele = flip $ foldr (either (insertVar . fst) (\ i -> insertIdent (i,Clock)))

insertAIdent :: AIdent -> Env -> Env
insertAIdent (AIdent (_,x)) = insertIdent (x,Variable)

insertAIdents :: [AIdent] -> Env -> Env
insertAIdents  = flip $ foldr insertAIdent

getLoc :: (Int,Int) -> Resolver Loc
getLoc l = Loc <$> asks envModule <*> pure l

getLoc' :: AIdent -> Resolver Loc
getLoc' (AIdent (l,x)) = getLoc l

unAIdent :: AIdent -> Ident
unAIdent (AIdent (_,x)) = x

resolveClock :: AIdent -> Resolver CTT.Clock
resolveClock (AIdent (l,x)) = do
  modClock <- asks envModule
  vars <- asks variables
  case (x,lookup x vars) of
    ("k0",_)       -> return $ CTT.Clock x
    (_,Just Clock) -> return $ CTT.Clock x
    _ -> throwError $ "Cannot resolve name " ++ x ++ " at position " ++
                      show l ++ " in module " ++ modClock

resolveName :: AIdent -> Resolver C.Name
resolveName (AIdent (l,x)) = do
  modName <- asks envModule
  vars <- asks variables
  case lookup x vars of
    Just Name -> return $ C.Name x
    _ -> throwError $ "Cannot resolve name " ++ x ++ " at position " ++
                      show l ++ " in module " ++ modName

resolveVar :: AIdent -> Resolver Ter
resolveVar (AIdent (l,x)) = do
  modName <- asks envModule
  vars    <- asks variables
  case lookup x vars of
    Just Variable    -> return $ CTT.Var x
    Just Constructor -> return $ CTT.Con x []
    Just PConstructor -> throwError $ "The path constructor " ++ x ++ " is used as a"
                                   ++ " variable at " ++ show l ++ " in " ++ modName
                                   ++ " (path constructors should have their type in"
                                   ++ " curly braces as first argument)"
    Just Name        ->
     throwError $ "Name " ++ x ++ " used as a variable at position " ++
                   show l ++ " in module " ++ modName
    _ -> throwError $ "Cannot resolve variable " ++ x ++ " at position " ++
                      show l ++ " in module " ++ modName

lam :: (Ident,Exp) -> Resolver Ter -> Resolver Ter
lam (a,t) e = CTT.Lam a <$> resolveExp t <*> local (insertVar a) e

lams :: [(Ident,Exp)] -> Resolver Ter -> Resolver Ter
lams = flip $ foldr lam

path :: AIdent -> Resolver Ter -> Resolver Ter
path i e = CTT.Path (C.Name (unAIdent i)) <$> local (insertName i) e

paths :: [AIdent] -> Resolver Ter -> Resolver Ter
paths [] _ = throwError "Empty path abstraction"
paths xs e = foldr path e xs

prev :: AIdent -> Resolver Ter -> Resolver Ter
prev k e = CTT.Prev (CTT.Clock (unAIdent k)) <$> local (insertClock k) e

clam :: AIdent -> Resolver Ter -> Resolver Ter
clam k e = CTT.CLam (CTT.Clock (unAIdent k)) <$> local (insertClock k) e

clams :: [AIdent] -> Resolver Ter -> Resolver Ter
clams [] _ = throwError "Empty clock abstraction"
clams xs e = foldr clam e xs

forall :: AIdent -> Resolver Ter -> Resolver Ter
forall k e = CTT.Forall (CTT.Clock (unAIdent k)) <$> local (insertClock k) e

foralls :: [AIdent] -> Resolver Ter -> Resolver Ter
foralls [] _ = throwError "Empty clock quantification"
foralls xs e = foldr forall e xs

bind :: (Ter -> Ter) -> (Ident,Exp) -> Resolver Ter -> Resolver Ter
bind f (x,t) e = f <$> lam (x,t) e

binds :: (Ter -> Ter) -> [(Ident,Exp)] -> Resolver Ter -> Resolver Ter
binds f = flip $ foldr $ bind f

bindTele :: (Ter -> Ter) -> [Either (Ident,Exp) Ident] -> Resolver Ter -> Resolver Ter
bindTele f = flip $ foldr (either (bind f) (\ i -> forall (AIdent (undefined,i))))

absTele :: [Either (Ident,Exp) Ident] -> Resolver Ter -> Resolver Ter
absTele = flip $ foldr (either lam (\ i -> clam (AIdent (undefined,i))))

resolveApps :: Exp -> [Exp] -> Resolver Ter
resolveApps x xs = mkApps <$> resolveExp x <*> mapM resolveExp xs

resolveExp :: Exp -> Resolver Ter
resolveExp e = case e of
  U             -> return CTT.U
  Var x         -> resolveVar x
  App t s       -> resolveApps x xs
    where (x,xs) = unApps t [s]
  Sigma ptele b -> do
    tele <- flattenPTele ptele
    binds CTT.Sigma tele (resolveExp b)
  Pi ptele b    -> do
    tele <- flattenPTele ptele
    binds CTT.Pi tele (resolveExp b)
  Fun a b       -> bind CTT.Pi ("_",a) (resolveExp b)
  Lam ptele t   -> do
    tele <- flattenPTele ptele
    lams tele (resolveExp t)
  Fst t         -> CTT.Fst <$> resolveExp t
  Snd t         -> CTT.Snd <$> resolveExp t
  Pair t0 ts    -> do
    e  <- resolveExp t0
    es <- mapM resolveExp ts
    return $ foldr1 CTT.Pair (e:es)
  Let decls e   -> do
    (rdecls,names) <- resolveDecls decls
    mkWheres rdecls <$> local (insertIdents names) (resolveExp e)
  Path is e     -> paths is (resolveExp e)
  Hole (HoleIdent (l,_)) -> CTT.Hole <$> getLoc l
  AppFormula t phi ->
    let (x,xs,phis) = unAppsFormulas e []
    in case x of
      PCon n a ->
        CTT.PCon (unAIdent n) <$> resolveExp a <*> mapM resolveExp xs
                              <*> mapM resolveFormula phis
      _ -> CTT.AppFormula <$> resolveExp t <*> resolveFormula phi
  IdP a u v     -> CTT.IdP <$> resolveExp a <*> resolveExp u <*> resolveExp v
  Comp u v ts   -> CTT.Comp <$> resolveExp u <*> resolveExp v <*> resolveSystem ts
  Fill u v ts   -> CTT.Fill <$> resolveExp u <*> resolveExp v <*> resolveSystem ts
  Trans u v     -> CTT.Comp <$> resolveExp u <*> resolveExp v <*> pure Map.empty
  Glue u ts     -> CTT.Glue <$> resolveExp u <*> resolveSystem ts
  GlueElem u ts -> CTT.GlueElem <$> resolveExp u <*> resolveSystem ts
  Later k ds t -> do
    k' <- resolveClock k
    (rds,names) <- resolveDelSubst ds
    l <- getLoc' k
    CTT.Later  l k' rds <$> local (insertIdents names) (resolveExp t)
  LaterEmp k t -> resolveExp (Later k (DelSubst []) t)
  Next k ds t sys -> do
    k' <- resolveClock k
    (rds,names) <- resolveDelSubst ds
    l <- getLoc' k
    CTT.Next l k' rds <$> local (insertIdents names) (resolveExp t) <*> resolveSystem sys
  NextEmp k t -> resolveExp (Next k (DelSubst []) t (System []))
  DFix k a t -> CTT.DFix <$> resolveClock k <*> resolveExp a <*> resolveExp t
  Prev k t -> prev k (resolveExp t)
  Forall ks t -> foralls ks (resolveExp t)
  CLam ks t   -> clams ks (resolveExp t)
  CApp t k    -> CTT.CApp <$> resolveExp t <*> resolveClock k
  -- Some sugar for fix's
  Fix k phi a t -> do
    let la = Later k (DelSubst []) a
    let recvar = AIdent ((0,0), unAIdent phi)
    let rec = DeclDef recvar [Tele phi [] la] a (NoWhere t)
    resolveExp $ Let [rec] (App (Var recvar) (DFix k a (Var recvar)))
  _ -> do
    modName <- asks envModule
    throwError ("Could not resolve " ++ show e ++ " in module " ++ modName)

resolveWhere :: ExpWhere -> Resolver Ter
resolveWhere = resolveExp . unWhere

resolveSystem :: System -> Resolver (C.System Ter)
resolveSystem (System ts) = do
  ts' <- sequence [ (,) <$> resolveFace alpha <*> resolveExp u
                  | Side alpha u <- ts ]
  let alphas = map fst ts'
  unless (nub alphas == alphas) $
    throwError $ "system contains same face multiple times: " ++ C.showListSystem ts'
  -- Note: the symbols in alpha are in scope in u, but they mean 0 or 1
  return $ Map.fromList ts'

resolveFace :: [Face] -> Resolver C.Face
resolveFace alpha =
  Map.fromList <$> sequence [ (,) <$> resolveName i <*> resolveDir d
                            | Face i d <- alpha ]

resolveDir :: Dir -> Resolver C.Dir
resolveDir Dir0 = return 0
resolveDir Dir1 = return 1

resolveFormula :: Formula -> Resolver C.Formula
resolveFormula (Dir d)          = C.Dir <$> resolveDir d
resolveFormula (Atom i)         = C.Atom <$> resolveName i
resolveFormula (Neg phi)        = negFormula <$> resolveFormula phi
resolveFormula (Conj phi _ psi) =
    andFormula <$> resolveFormula phi <*> resolveFormula psi
resolveFormula (Disj phi psi)   =
    orFormula <$> resolveFormula phi <*> resolveFormula psi

resolveBranch :: Branch -> Resolver CTT.Branch
resolveBranch (OBranch (AIdent (_,lbl)) args e) = do
  re <- local (insertAIdents args) $ resolveWhere e
  return $ CTT.OBranch lbl (map unAIdent args) re
resolveBranch (PBranch (AIdent (_,lbl)) args is e) = do
  re <- local (insertNames is . insertAIdents args) $ resolveWhere e
  let names = map (C.Name . unAIdent) is
  return $ CTT.PBranch lbl (map unAIdent args) names re

resolveTele :: [Either (Ident,Exp) Ident] -> Resolver CTT.Tele
resolveTele []        = return []
resolveTele (Left (i,d):t) =
  ((i,) <$> resolveExp d) <:> local (insertVar i) (resolveTele t)

resolveLabel :: [(Ident,SymKind)] -> Label -> Resolver CTT.Label
resolveLabel _ (OLabel n vdecl) =
  CTT.OLabel (unAIdent n) <$> resolveTele (flattenTele vdecl)
resolveLabel cs (PLabel n vdecl is sys) = do
  let tele' = flattenTele vdecl
      names = map (C.Name . unAIdent) is
      n'    = unAIdent n
      cs'   = delete (n',PConstructor) cs
  CTT.PLabel n' <$> resolveTele tele' <*> pure names
                <*> local (insertNames is . insertIdents cs' . insertTele tele')
                      (resolveSystem sys)

resolveDelSubst :: DelSubst -> Resolver (CTT.DelSubst,[(Ident,SymKind)])
resolveDelSubst (DelSubst ds) = resolveDelSubst' (DelSubst (reverse ds))

resolveDelSubst' :: DelSubst -> Resolver (CTT.DelSubst,[(Ident,SymKind)])
resolveDelSubst' (DelSubst ((DelBind (AIdent (_,f)) a t) : ds)) = do
                     (rds, idents) <- resolveDelSubst' (DelSubst ds)
                     rt <- resolveExp t
                     ra <- local (insertIdents idents) $ resolveExp a
                     return ((CTT.DelBind (f, (Just ra, rt))) : rds, (f, Variable) : idents)
resolveDelSubst' (DelSubst ((DelBindI (AIdent (_,f)) t) : ds)) = do
                     (rds, idents) <- resolveDelSubst' (DelSubst ds)
                     rt <- resolveExp t
                     return ((CTT.DelBind (f, (Nothing, rt))) : rds, (f, Variable) : idents)
resolveDelSubst' (DelSubst []) = return ([],[])

-- Resolve Data or Def or Split declarations
resolveDecl :: Decl -> Resolver (CTT.Decl,[(Ident,SymKind)])
resolveDecl d = case d of
  DeclDef (AIdent (_,f)) tele t body -> do
    let tele' = flattenTele tele
    a <- bindTele CTT.Pi tele' (resolveExp t)
    d <- absTele tele' (local (insertVar f) $ resolveWhere body)
    return ((f,(a,d)),[(f,Variable)])
  DeclData (AIdent (l,f)) tele sums -> do
    let tele' = flattenTele tele
    a <- bindTele CTT.Pi tele' (return CTT.U)
    let cs  = [ (unAIdent lbl,Constructor) | OLabel lbl _ <- sums ]
    let pcs = [ (unAIdent lbl,PConstructor) | PLabel lbl _ _ _ <- sums ]
    let sum = if null pcs then CTT.Sum else CTT.HSum
    d <- absTele tele' $ local (insertVar f) $
         sum <$> getLoc l <*> pure f
             <*> mapM (resolveLabel (cs ++ pcs)) sums
    return ((f,(a,d)),(f,Variable):cs ++ pcs)
  DeclFix phi@(AIdent (l,f)) tele t k e -> do
    let tele' = flattenTele tele
    a    <- bindTele CTT.Pi tele' (resolveExp t)
    body <- absTele tele' (resolveExp $ Fix k phi t e)
    return ((f,(a,body)),[(f,Variable)])

  DeclSplit (AIdent (l,f)) tele t brs -> do
    let tele' = flattenTele tele
    loc  <- getLoc l
    a    <- bindTele CTT.Pi tele' (resolveExp t)
    ty   <- local (insertTele tele') $ resolveExp t
    brs' <- local (insertVar f . insertTele tele') (mapM resolveBranch brs)
    body <- absTele tele' (return $ CTT.Split f loc ty brs')
    return ((f,(a,body)),[(f,Variable)])
  DeclUndef (AIdent (l,f)) tele t -> do
    let tele' = flattenTele tele
    a <- bindTele CTT.Pi tele' (resolveExp t)
    d <- CTT.Undef <$> getLoc l <*> pure a
    return ((f,(a,d)),[(f,Variable)])

resolveDecls :: [Decl] -> Resolver ([[CTT.Decl]],[(Ident,SymKind)])
resolveDecls []     = return ([],[])
resolveDecls (d:ds) = do
  (rtd,names)  <- resolveDecl d
  (rds,names') <- local (insertIdents names) $ resolveDecls ds
  return ([rtd] : rds, names' ++ names)

resolveModule :: Module -> Resolver ([[CTT.Decl]],[(Ident,SymKind)])
resolveModule (Module (AIdent (_,n)) _ decls) =
  local (updateModule n) $ resolveDecls decls

resolveModules :: [Module] -> Resolver ([[CTT.Decl]],[(Ident,SymKind)])
resolveModules []         = return ([],[])
resolveModules (mod:mods) = do
  (rmod, names)  <- resolveModule mod
  (rmods,names') <- local (insertIdents names) $ resolveModules mods
  return (rmod ++ rmods, names' ++ names)
