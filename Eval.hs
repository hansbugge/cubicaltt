{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Debug.Trace
import Control.Monad
import Data.List
import Data.Monoid ((<>), mempty)
import Data.Maybe (fromMaybe)
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey
                ,elems,intersectionWith,intersection,keys)
import qualified Data.Map as Map

import Connections
import CTT

look :: String -> Env -> Val
look x (Upd y rho,v:vs,fs,ws) | x == y = v
                              | otherwise = look x (rho,vs,fs,ws)
look x r@(Def decls rho,vs,fs,ws) = case lookup x decls of
  Just (_,t) -> eval r t
  Nothing    -> look x (rho,vs,fs,ws)
look x r@(DelDef ds rho,vs,fs,ws) = case lookup x (map (\(DelBind x) -> x) ds) of
  Just (_,v) -> Ter (Var x) r
  Nothing    -> look x (rho,vs,fs,ws)
look x (Sub _ rho,vs,_:fs,ws) = look x (rho,vs,fs,ws)
look x r@(DelUpd y rho,vs,fs,w:ws) | x == y = Ter (Var y) r
                                   | otherwise  = look x (rho,vs,fs,ws)

lookDel :: String -> Env -> Either Val Val
lookDel x (Upd y rho,v:vs,fs,ws) | x == y = Left v
                                 | otherwise = lookDel x (rho,vs,fs,ws)
lookDel x r@(Def decls rho,vs,fs,ws) = case lookup x decls of
  Just (_,t) -> Left (eval r t)
  Nothing    -> lookDel x (rho,vs,fs,ws)
lookDel x r@(DelDef ds rho,vs,fs,ws) = case lookup x (map (\(DelBind x) -> x) ds) of
  Just (_,v) -> Right v
  Nothing    -> lookDel x (rho,vs,fs,ws)
lookDel x (Sub _ rho,vs,_:fs,ws) = lookDel x (rho,vs,fs,ws)
lookDel x (DelUpd y rho,vs,fs,w:ws) | x == y = Right w
                                    | otherwise  = lookDel x (rho,vs,fs,ws)

lookType :: String -> Env -> Val
lookType x (Upd y rho,VVar _ a:vs,fs,ws)
  | x == y    = a
  | otherwise = lookType x (rho,vs,fs,ws)
lookType x r@(Def decls rho,vs,fs,ws) = case lookup x decls of
  Just (a,_) -> eval r a
  Nothing -> lookType x (rho,vs,fs,ws)
lookType x r@(DelDef ds rho,vs,fs,ws) = case lookup x (map (\(DelBind x) -> x) ds) of
  Just (a,_) -> a
  Nothing -> lookType x (rho,vs,fs,ws)
lookType x (Sub _ rho,vs,_:fs,ws) = lookType x (rho,vs,fs,ws)
lookType x (DelUpd y rho,vs,fs,VVar _ a:ws) -- correct?
  | x == y    = a
  | otherwise = lookType x (rho,vs,fs,ws)


lookName :: Name -> Env -> Formula
-- lookName i Empty       = error $ "lookName: not found " ++ show i
lookName i (Upd _ rho,v:vs,fs,ws)    = lookName i (rho,vs,fs,ws)
lookName i (DelUpd _ rho,vs,fs,w:ws) = lookName i (rho,vs,fs,ws)
lookName i (Def _ rho,vs,fs,ws)      = lookName i (rho,vs,fs,ws)
lookName i (DelDef _ rho,vs,fs,ws)      = lookName i (rho,vs,fs,ws)
lookName i (Sub j rho,vs,phi:fs,ws) | i == j    = phi
                                    | otherwise = lookName i (rho,vs,fs,ws)

todo = True

-----------------------------------------------------------------------
-- Nominal instances

instance Nominal Ctxt where
  support _ = []
  act e _   = e
  swap e _  = e

instance Nominal Val where
  support v = case v of
    VU                      -> []
    Ter _ e                 -> support e
    VPi u v                 -> support [u,v]
    VComp a u ts            -> support (a,u,ts)
    VIdP a v0 v1            -> support [a,v0,v1]
    VPath i v               -> i `delete` support v
    VTrans u v              -> support (u,v)
    VSigma u v              -> support (u,v)
    VPair u v               -> support (u,v)
    VFst u                  -> support u
    VSnd u                  -> support u
    VCon _ vs               -> support vs
    VPCon _ a vs phis       -> support (a,vs,phis)
    VVar _ v                -> support v
    VApp u v                -> support (u,v)
    VLam _ u v              -> support (u,v)
    VAppFormula u phi       -> support (u,phi)
    VSplit u v              -> support (u,v)
    VGlue a ts              -> support (a,ts)
    VGlueElem a ts          -> support (a,ts)
    VGlueLine a phi psi     -> support (a,phi,psi)
    VGlueLineElem a phi psi -> support (a,phi,psi)
    VCompElem a es u us     -> support (a,es,u,us)
    VElimComp a es u        -> support (a,es,u)
    -- VLater _ e -> support e
    VLater v -> support v
    -- VNext _ e -> support e
    VNext v -> support v
    VFix a v -> support (a,v)

  act u (i, phi) | i `notElem` support u = u
                 | otherwise =
    let acti :: Nominal a => a -> a
        acti u = act u (i, phi)
        sphi = support phi
    in case u of
         VU           -> VU
         Ter t e      -> Ter t (acti e)
         VPi a f      -> VPi (acti a) (acti f)
         VComp a v ts -> compLine (acti a) (acti v) (acti ts)
         VIdP a u v   -> VIdP (acti a) (acti u) (acti v)
         VPath j v | j == i -> u
                   | j `notElem` sphi -> VPath j (acti v)
                   | otherwise -> VPath k (acti (v `swap` (j,k)))
              where k = fresh (v,Atom i,phi)
         VTrans u v              -> transLine (acti u) (acti v)
         VSigma a f              -> VSigma (acti a) (acti f)
         VPair u v               -> VPair (acti u) (acti v)
         VFst u                  -> fstVal (acti u)
         VSnd u                  -> sndVal (acti u)
         VCon c vs               -> VCon c (acti vs)
         VPCon c a vs phis       -> pcon c (acti a) (acti vs) (acti phis)
         VVar x v                -> VVar x (acti v)
         VAppFormula u psi       -> acti u @@ acti psi
         VApp u v                -> app todo (acti u) (acti v)
         VLam x t u              -> VLam x (acti t) (acti u)
         VSplit u v              -> app todo (acti u) (acti v)
         VGlue a ts              -> glue (acti a) (acti ts)
         VGlueElem a ts          -> glueElem (acti a) (acti ts)
         VGlueLine a phi psi     -> glueLine (acti a) (acti phi) (acti psi)
         VGlueLineElem a phi psi -> glueLineElem (acti a) (acti phi) (acti psi)
         VCompElem a es u us     -> compElem (acti a) (acti es) (acti u) (acti us)
         VElimComp a es u        -> elimComp (acti a) (acti es) (acti u)
         -- VLater a e -> VLater a (acti e)
         VLater v -> VLater (acti v)
         -- VNext t e -> VNext t (acti e)
         VNext v -> VNext (acti v)

  -- This increases efficiency as it won't trigger computation.
  swap u ij@(i,j) =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU                      -> VU
         Ter t e                 -> Ter t (sw e)
         VPi a f                 -> VPi (sw a) (sw f)
         VComp a v ts            -> VComp (sw a) (sw v) (sw ts)
         VIdP a u v              -> VIdP (sw a) (sw u) (sw v)
         VPath k v               -> VPath (swapName k ij) (sw v)
         VTrans u v              -> VTrans (sw u) (sw v)
         VSigma a f              -> VSigma (sw a) (sw f)
         VPair u v               -> VPair (sw u) (sw v)
         VFst u                  -> VFst (sw u)
         VSnd u                  -> VSnd (sw u)
         VCon c vs               -> VCon c (sw vs)
         VPCon c a vs phis       -> VPCon c (sw a) (sw vs) (sw phis)
         VVar x v                -> VVar x (sw v)
         VAppFormula u psi       -> VAppFormula (sw u) (sw psi)
         VApp u v                -> VApp (sw u) (sw v)
         VLam x u v              -> VLam x (sw u) (sw v)
         VSplit u v              -> VSplit (sw u) (sw v)
         VGlue a ts              -> VGlue (sw a) (sw ts)
         VGlueElem a ts          -> VGlueElem (sw a) (sw ts)
         VGlueLine a phi psi     -> VGlueLine (sw a) (sw phi) (sw psi)
         VGlueLineElem a phi psi -> VGlueLineElem (sw a) (sw phi) (sw psi)
         VCompElem a es u us     -> VCompElem (sw a) (sw es) (sw u) (sw us)
         VElimComp a es u        -> VElimComp (sw a) (sw es) (sw u)
         VLater v                -> VLater (sw v)
         VNext v                 -> VNext (sw v)
         VFix a v                -> VFix (sw a) (sw v)
         v -> error $ "swap:\n" ++ show v ++ "\n not handled"

instance Nominal Ter where
-----------------------------------------------------------------------
-- The evaluator

eval' :: Bool -> Env -> Ter -> Val
eval' b rho v = case v of
  U                   -> VU
  App r s             -> app b (eval' b rho r) (eval' b rho s)
  Var i               -> look i rho
  Pi t@(Lam _ a _)    -> VPi (eval' b rho a) (eval' b rho t)
  Sigma t@(Lam _ a _) -> VSigma (eval' b rho a) (eval' b rho t)
  Pair x y            -> VPair (eval' b rho x) (eval' b rho y)
  Fst a               -> fstVal (eval' b rho a)
  Snd a               -> sndVal (eval' b rho a)
  Where t decls       -> eval' b (def decls rho) t
  Con name ts         -> VCon name (map (eval' b rho) ts)
  PCon name a ts phis  ->
    pcon name (eval' b rho a) (map (eval' b rho) ts) (map (evalFormula rho) phis)
  Lam{}               -> Ter v rho
  Split{}             -> Ter v rho
  Sum{}               -> Ter v rho
  Undef{}             -> Ter v rho
  Hole{}              -> Ter v rho
  IdP a e0 e1         -> VIdP (eval' b rho a) (eval' b rho e0) (eval' b rho e1)
  Path i t            ->
    let j = fresh rho
    in VPath j (eval' b (sub (i,Atom j) rho) t)
  Trans u v           -> transLine (eval' b rho u) (eval' b rho v)
  AppFormula e phi    -> eval' b rho e @@ evalFormula rho phi
  Comp a t0 ts        -> compLine (eval' b rho a) (eval' b rho t0) (evalSystem rho ts)
  Glue a ts           -> glue (eval' b rho a) (evalSystem rho ts)
  GlueElem a ts       -> glueElem (eval' b rho a) (evalSystem rho ts)
  GlueLine a phi psi  ->
    glueLine (eval' b rho a) (evalFormula rho phi) (evalFormula rho psi)
  GlueLineElem a phi psi ->
    glueLineElem (eval' b rho a) (evalFormula rho phi) (evalFormula rho psi)
  CompElem a es u us  -> compElem (eval' b rho a) (evalSystem rho es) (eval' b rho u)
                                  (evalSystem rho us)
  ElimComp a es u     -> elimComp (eval' b rho a) (evalSystem rho es) (eval' b rho u)
  Later xi t          -> VLater (eval (pushDelSubst (evalDelSubst rho xi) rho) t)
  Next xi t           -> VNext  (eval (pushDelSubst (evalDelSubst rho xi) rho) t)
  Fix a t  | b           -> app b (eval' b rho t) (VNext (VFix (eval rho a) (eval rho t)))
           | otherwise -> app b (eval' b rho t) (VNext (Ter (Fix a t) rho))
  _                   -> error $ "Cannot evaluate " ++ show v

eval :: Env -> Ter -> Val
eval = eval' True

evalDel :: Env -> Ter -> Val
evalDel = eval' False

evalDelSubst :: Env -> DelSubst -> VDelSubst
evalDelSubst rho ds = case ds of
  []                        -> []
  (DelBind (f,(a,t)):ds')   -> DelBind (f, (eval rho a, eval rho t))
                                 : evalDelSubst rho ds'

pushDelSubst :: VDelSubst -> Env -> Env
pushDelSubst [] rho = rho
pushDelSubst (DelBind (f,(_va,vt)) : ds) rho =
  case vt of
   -- VNext t' rho' -> upd    (f,eval rho' t') (pushDelSubst ds rho)
   VNext v       -> upd (f, v) (pushDelSubst ds rho) -- v has been evalDel'd not eval'd
   _             -> delUpd (f,vt)           (pushDelSubst ds rho)


unfoldOneFix :: Val -> Val
unfoldOneFix (VFix a v) = app True v (VNext (VFix a v))
unfoldOneFix (VLater v) = VLater (unfoldOneFix v)
unfoldOneFix (VIdP v1 v2 v3) = VIdP (unfoldOneFix v1) (unfoldOneFix v2) (unfoldOneFix v3)
unfoldOneFix (VPath n v) = VPath n (unfoldOneFix v)
unfoldOneFix v = v -- TODO: rest of this pattern matching


evalFormula :: Env -> Formula -> Formula
evalFormula rho phi = case phi of
  Atom i         -> lookName i rho
  NegAtom i      -> negFormula (lookName i rho)
  phi1 :/\: phi2 -> evalFormula rho phi1 `andFormula` evalFormula rho phi2
  phi1 :\/: phi2 -> evalFormula rho phi1 `orFormula` evalFormula rho phi2
  _              -> phi

evals :: Env -> [(Ident,Ter)] -> [(Ident,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

evalSystem :: Env -> System Ter -> System Val
evalSystem rho ts =
  let out = concat [ let betas = meetss [ invFormula (lookName i rho) d
                                        | (i,d) <- assocs alpha ]
                     in [ (beta,eval (rho `face` beta) talpha) | beta <- betas ]
                   | (alpha,talpha) <- assocs ts ]
  in mkSystem out

app :: Bool -> Val -> Val -> Val
app b u v = case (u,v) of -- trace ("app: " ++ show u ++ " $ " ++ show v) $ case (u,v) of
--  (VLam _ _ b,_)                      -> b -- assuming b is closed
  (Ter (Lam x _ t) e,_)               -> eval' b (upd (x,v) e) t
  (Ter (Split _ _ _ nvs) e,VCon c vs) -> case lookupBranch c nvs of
    Just (OBranch _ xs t) -> eval' b (upds (zip xs vs) e) t
    _     -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ _ nvs) e,VPCon c _ us phis) -> case lookupBranch c nvs of
    Just (PBranch _ xs is t) -> eval' b (subs (zip is phis) (upds (zip xs us) e)) t
    _ -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ ty hbr) e,VComp a w ws) -> case eval' b e ty of
    VPi _ f -> let j   = fresh (e,v)
                   wsj = Map.map (@@ j) ws
                   w'  = app b u w
                   ws' = mapWithKey (\alpha -> app b (u `face` alpha)) wsj
               in genComp j (app b f (fill j a w wsj)) w' ws'
    _ -> error $ "app: Split annotation not a Pi type " ++ show u
  (Ter Split{} _,_) | isNeutral v         -> VSplit u v
  (Ter Split{} _,VCompElem _ _ w _)       -> app b u w
  (Ter Split{} _,VElimComp _ _ w)         -> app b u w
  (VTrans (VPath i (VPi a f)) li0,vi1) ->
    let j       = fresh (u,vi1)
        (aj,fj) = (a,f) `swap` (i,j)
        v       = transFillNeg j aj vi1
        vi0     = transNeg j aj vi1
    in trans j (app b fj v) (app b li0 vi0)
  (VComp (VPi a f) li0 ts,vi1) ->
    let j   = fresh (u,vi1)
        tsj = Map.map (@@ j) ts
    in comp j (app b f vi1) (app b li0 vi1)
              (intersectionWith (app b) tsj (border vi1 tsj))
  _ | isNeutral u       -> VApp u v
  (VCompElem _ _ u _,_) -> app b u v
  (VElimComp _ _ u,_)   -> app b u v
  _                     -> error $ "app " ++ show b ++ "\n  " ++ show u ++ "\n  " ++ show v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
fstVal (VElimComp _ _ u) = fstVal u
fstVal (VCompElem _ _ u _) = fstVal u
fstVal u | isNeutral u = VFst u
fstVal u               = error $ "fstVal: " ++ show u ++ " is not neutral."
sndVal (VPair a b)     = b
sndVal (VElimComp _ _ u) = sndVal u
sndVal (VCompElem _ _ u _) = sndVal u
sndVal u | isNeutral u = VSnd u
sndVal u               = error $ "sndVal: " ++ show u ++ " is not neutral."

-- infer the type of a neutral value
inferType :: Val -> Val
inferType v = case v of
  VVar _ t -> t
  Ter (Undef _ t) rho -> eval rho t
  VFst t -> case inferType t of
    VSigma a _ -> a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> case inferType t of
    VSigma _ f -> app todo f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit s@(Ter (Split _ _ t _) rho) v1 -> case eval rho t of
    VPi _ f -> app todo f v1
    ty      -> error $ "inferType: Pi type expected for split annotation in "
               ++ show v ++ ", got " ++ show ty
  VApp t0 t1 -> case inferType t0 of
    VPi _ f -> app todo f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  VAppFormula t phi -> case inferType t of
    VIdP a _ _ -> a @@ phi
    ty         -> error $ "inferType: expected IdP type for " ++ show v
                  ++ ", got " ++ show ty
  VComp a _ _ -> a
  VTrans a _  -> a @@ One
  Ter (Var x) rho -> case lookDel x rho of
                       Left v  -> inferType v
                       Right v -> case inferType v of
                                    VLater w -> w
                                    w -> error $ "inferType: not a later: \n" ++ show w
  _ -> error $ "inferType: not neutral " ++ show v

(@@) :: ToFormula a => Val -> a -> Val
(VPath i u) @@ phi         = u `act` (i,toFormula phi)
v@(Ter Hole{} _) @@ phi    = VAppFormula v (toFormula phi)
v @@ phi | isNeutral v     = case (inferType v,toFormula phi) of
  (VIdP  _ a0 _,Dir 0) -> a0
  (VIdP  _ _ a1,Dir 1) -> a1
  _  -> VAppFormula v (toFormula phi)
(VCompElem _ _ u _) @@ phi = u @@ phi
(VElimComp _ _ u) @@ phi   = u @@ phi
v @@ phi                   = error $ "(@@): " ++ show v ++ " should be neutral."

pcon :: LIdent -> Val -> [Val] -> [Formula] -> Val
pcon c a@(Ter (Sum _ _ lbls) rho) us phis = case lookupPLabel c lbls of
  -- TODO: is this correct? Double check!
  Just (tele,is,ts) | eps `Map.member` vs -> vs ! eps
                    | otherwise -> VPCon c a us phis
    where rho' = subs (zip is phis) (updsTele tele us rho)
          vs   = evalSystem rho' ts
  Nothing           -> error "pcon"
-- pcon c a us phi     = VPCon c a us phi

-----------------------------------------------------------
-- Transport

transLine :: Val -> Val -> Val
transLine u v = trans i (u @@ i) v
  where i = fresh (u,v)

transNegLine :: Val -> Val -> Val
transNegLine u v = transNeg i (u @@ i) v
  where i = fresh (u,v)

trans :: Name -> Val -> Val -> Val
trans i v0 v1 | i `notElem` support v0 = v1
trans i v0 v1 = case (v0,v1) of
  (VIdP a u v,w) ->
    let j   = fresh (Atom i,v0,w)
        ts' = mkSystem [(j ~> 0,u),(j ~> 1,v)]
    in VPath j $ genComp i (a @@ j) (w @@ j) ts'
  (VSigma a f,u) ->
    let (u1,u2) = (fstVal u,sndVal u)
        fill_u1 = transFill i a u1
        ui1     = trans i a u1
        comp_u2 = trans i (app todo f fill_u1) u2
    in VPair ui1 comp_u2
  (VPi{},_) -> VTrans (VPath i v0) v1
  (Ter (Sum _ _ nass) env,VCon c us) -> case lookupLabel c nass of
    Just as -> VCon c $ transps i as env us
    Nothing -> error $ "trans: missing constructor " ++ c ++ " in " ++ show v0
  (Ter (Sum _ _ nass) env,VPCon c _ ws0 phis) -> case lookupLabel c nass of
    -- v1 should be independent of i, so i # phi
    Just as -> VPCon c (v0 `face` (i ~> 1)) (transps i as env ws0) phis
    Nothing -> error $ "trans: missing path constructor " ++ c ++
                       " in " ++ show v0
  _ | isNeutral w -> w
    where w = VTrans (VPath i v0) v1
  (Ter (Sum _ _ nass) env,VElimComp _ _ u) -> trans i v0 u
  (Ter (Sum _ _ nass) env,VCompElem _ _ u _) -> trans i v0 u
  (VGlue a ts,_)    -> transGlue i a ts v1
  (VGlueLine a phi psi,_) -> transGlueLine i a phi psi v1
  (VComp VU a es,_) -> transU i a es v1
  (Ter (Sum _ _ nass) env,VComp b w ws) -> comp k v01 (trans i v0 w) ws'
    where v01 = v0 `face` (i ~> 1)  -- b is vi0 and independent of j
          k   = fresh (v0,v1,Atom i)
          transp alpha w = trans i (v0 `face` alpha) (w @@ k)
          ws'          = mapWithKey transp ws
  _ -> error $ "trans not implemented for v0 = " ++ show v0
            ++ "\n and v1 = " ++ show v1

transNeg :: Name -> Val -> Val -> Val
transNeg i a u = trans i (a `sym` i) u

transFill, transFillNeg :: Name -> Val -> Val -> Val
transFill i a u = trans j (a `conj` (i,j)) u
  where j = fresh (Atom i,a,u)
transFillNeg i a u = (transFill i (a `sym` i) u) `sym` i

transps :: Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
transps i []         _ []     = []
transps i ((x,a):as) e (u:us) =
  let v   = transFill i (eval e a) u
      vi1 = trans i (eval e a) u
      vs  = transps i as (upd (x,v) e) us
  in vi1 : vs
transps _ _ _ _ = error "transps: different lengths of types and values"

-- Given u of type a "squeeze i a u" connects in the direction i
-- trans i a u(i=0) to u(i=1)
squeeze :: Name -> Val -> Val -> Val
squeeze i a u = trans j (a `disj` (i,j)) u
  where j = fresh (Atom i,a,u)

squeezeNeg :: Name -> Val -> Val -> Val
squeezeNeg i a u = transNeg j (a `conj` (i,j)) u
  where j = fresh (Atom i,a,u)

-------------------------------------------------------------------------------
-- Composition

compLine :: Val -> Val -> System Val -> Val
compLine a u ts = comp i a u (Map.map (@@ i) ts)
  where i = fresh (a,u,ts)

genComp, genCompNeg :: Name -> Val -> Val -> System Val -> Val
genComp i a u ts | Map.null ts = trans i a u
genComp i a u ts = comp i ai1 (trans i a u) ts'
  where ai1 = a `face` (i ~> 1)
        ts' = mapWithKey (\alpha -> squeeze i (a `face` alpha)) ts
genCompNeg i a u ts = genComp i (a `sym` i) u (ts `sym` i)

fillLine :: Val -> Val -> System Val -> Val
fillLine a u ts = VPath i $ fill i a u (Map.map (@@ i) ts)
  where i = fresh (a,u,ts)

fill, fillNeg :: Name -> Val -> Val -> System Val -> Val
fill i a u ts = comp j a u (ts `conj` (i,j))
  where j = fresh (Atom i,a,u,ts)
fillNeg i a u ts = (fill i a u (ts `sym` i)) `sym` i

genFill, genFillNeg :: Name -> Val -> Val -> System Val -> Val
genFill i a u ts = genComp j (a `conj` (i,j)) u (ts `conj` (i,j))
  where j = fresh (Atom i,a,u,ts)
genFillNeg i a u ts = (genFill i (a `sym` i) u (ts `sym` i)) `sym` i

comps :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps i []         _ []         = []
comps i ((x,a):as) e ((ts,u):tsus) =
  let v   = genFill i (eval e a) u ts
      vi1 = genComp i (eval e a) u ts
      vs  = comps i as (upd (x,v) e) tsus
  in vi1 : vs
comps _ _ _ _ = error "comps: different lengths of types and values"

-- i is independent of a and u
comp :: Name -> Val -> Val -> System Val -> Val
comp i a u ts | eps `Map.member` ts    = (ts ! eps) `face` (i ~> 1)
comp i a u ts | i `notElem` support ts = u
comp i a u ts | not (Map.null indep)   = comp i a u ts'
  where (ts',indep) = Map.partition (\t -> i `elem` support t) ts
comp i a u ts = case a of
  VIdP p _ _ -> let j = fresh (Atom i,a,u,ts)
                in VPath j $ comp i (p @@ j) (u @@ j) (Map.map (@@ j) ts)
  VSigma a f -> VPair ui1 comp_u2
    where (t1s, t2s) = (Map.map fstVal ts, Map.map sndVal ts)
          (u1,  u2)  = (fstVal u, sndVal u)
          fill_u1    = fill i a u1 t1s
          ui1        = comp i a u1 t1s
          comp_u2    = genComp i (app todo f fill_u1) u2 t2s
  VPi{} -> VComp a u (Map.map (VPath i) ts)
  VU -> VComp VU u (Map.map (VPath i) ts)
  _ | isNeutral w -> w
    where w = VComp a u (Map.map (VPath i) ts)
  VComp VU a es -> compU i a es u ts
  VGlue b hisos -> compGlue i b hisos u ts
  VGlueLine b phi psi -> compGlueLine i b phi psi u ts
  Ter (Sum _ _ nass) env -> case u of
    VCon n us -> case lookupLabel n nass of
      Just as ->
        if all isCon (elems ts)
           then let tsus = transposeSystemAndList (Map.map unCon ts) us
                in VCon n $ comps i as env tsus
           else VComp a u (Map.map (VPath i) ts)
      Nothing -> error $ "comp: missing constructor in labelled sum " ++ n
    VPCon{} -> VComp a u (Map.map (VPath i) ts)
    VComp{} -> VComp a u (Map.map (VPath i) ts)
    VCompElem _ _ u1 _  -> comp i a u1 ts
    VElimComp _ _ u1    -> comp i a u1 ts
    _ -> error $ "comp ter sum" ++ show u

compNeg :: Name -> Val -> Val -> System Val -> Val
compNeg i a u ts = comp i a u (ts `sym` i)

-- fills :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
-- fills i []         _ []         = []
-- fills i ((x,a):as) e ((ts,u):tsus) =
--   let v  = genFill i (eval e a) ts u
--       vs = fills i as (Upd e (x,v)) tsus
--   in v : vs
-- fills _ _ _ _ = error "fills: different lengths of types and values"

-------------------------------------------------------------------------------
-- | Glue
--
-- An hiso for a type b is a five-tuple: (a,f,g,r,s)   where
--  a : U
--  f : a -> b
--  g : b -> a
--  s : forall (y : b), f (g y) = y
--  t : forall (x : a), g (f x) = x

hisoDom :: Val -> Val
hisoDom (VPair a _) = a
hisoDom x           = error $ "HisoDom: Not an hiso: " ++ show x

hisoFun :: Val -> Val
hisoFun (VPair _ (VPair f _)) = f
hisoFun x                     = error $ "HisoFun: Not an hiso: " ++ show x

glue :: Val -> System Val -> Val
glue b ts | Map.null ts         = b
          | eps `Map.member` ts = hisoDom (ts ! eps)
          | otherwise           = VGlue b ts

glueElem :: Val -> System Val -> Val
glueElem v us | Map.null us         = v
              | eps `Map.member` us = us ! eps
              | otherwise           = VGlueElem v us

unGlue :: System Val -> Val -> Val
unGlue hisos w
    | Map.null hisos         = w
    | eps `Map.member` hisos = app todo (hisoFun (hisos ! eps)) w
    | otherwise              = case w of
       VGlueElem v us   -> v
       VElimComp _ _ v -> unGlue hisos v
       VCompElem a es v vs -> unGlue hisos v
       _ -> error $ "unGlue: " ++ show w ++ " should be neutral!"

transGlue :: Name -> Val -> System Val -> Val -> Val
transGlue i b hisos wi0 = glueElem vi1'' usi1
  where vi0  = unGlue (hisos `face` (i ~> 0)) wi0 -- in b(i0)

        vi1  = trans i b vi0           -- in b(i1)

        hisosI1 = hisos `face` (i ~> 1)
        hisos'' =
          filterWithKey (\alpha _ -> alpha `Map.notMember` hisos) hisosI1

        -- set of elements in hisos independent of i
        hisos' = filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos

        us'    = mapWithKey (\gamma isoG ->
                  transFill i (hisoDom isoG) (wi0 `face` gamma))
                 hisos'
        usi1'  = mapWithKey (\gamma isoG ->
                   trans i (hisoDom isoG) (wi0 `face` gamma))
                 hisos'

        ls'    = mapWithKey (\gamma isoG ->
                   VPath i $ squeeze i (b `face` gamma)
                           (app todo (hisoFun isoG) (us' ! gamma)))
                 hisos'
        bi1    = b `face` (i ~> 1)
        vi1'   = compLine bi1 vi1 ls'

        uls''   = mapWithKey (\gamma isoG ->
                     gradLemma (bi1 `face` gamma) isoG (usi1' `face` gamma)
                               (vi1' `face` gamma))
                   hisos''

        vi1''   = compLine bi1 vi1' (Map.map snd uls'')

        usi1    = mapWithKey (\gamma _ ->
                    if gamma `Map.member` usi1'
                       then usi1' ! gamma
                       else fst (uls'' ! gamma))
                  hisosI1

compGlue :: Name -> Val -> System Val -> Val -> System Val -> Val
compGlue i b hisos wi0 ws = glueElem vi1' usi1'
  where vs   = mapWithKey
                 (\alpha wAlpha -> unGlue (hisos `face` alpha) wAlpha) ws
        vi0  = unGlue hisos wi0 -- in b

        v    = fill i b vi0 vs           -- in b
        vi1  = comp i b vi0 vs           -- in b

        us'    = mapWithKey (\gamma isoG ->
                   fill i (hisoDom isoG) (wi0 `face` gamma) (ws `face` gamma))
                 hisos
        usi1'  = mapWithKey (\gamma isoG ->
                   comp i (hisoDom isoG) (wi0 `face` gamma) (ws `face` gamma))
                 hisos

        ls'    = mapWithKey (\gamma isoG ->
                   pathComp i (b `face` gamma) (v `face` gamma)
                   (app todo (hisoFun isoG) (us' ! gamma)) (vs `face` gamma))
                 hisos

        vi1'  = compLine b vi1 ls'

-- assumes u and u' : A are solutions of us + (i0 -> u(i0))
-- The output is an L-path in A(i1) between u(i1) and u'(i1)
pathComp :: Name -> Val -> Val -> Val -> System Val -> Val
pathComp i a u u' us = VPath j $ comp i a (u `face` (i ~> 0)) us'
  where j   = fresh (Atom i,a,us,u,u')
        us' = insertsSystem [(j ~> 0, u), (j ~> 1, u')] us


-- Grad Lemma, takes a iso an L-system ts a value v s.t. sigma us = border v
-- outputs u s.t. border u = us and an L-path between v and sigma u
-- an theta is a L path if L-border theta is constant
gradLemma :: Val -> Val -> System Val -> Val -> (Val, Val)
gradLemma b hiso@(VPair a (VPair f (VPair g (VPair s t)))) us v =
  (u, VPath i theta'')
  where i:j:_   = freshs (a,hiso,us,v)
        us'     = mapWithKey (\alpha uAlpha ->
                                   app todo (t `face` alpha) uAlpha @@ i) us
        theta   = fill i a (app todo g v) us'
        u       = comp i a (app todo g v) us'
        ws      = insertSystem (i ~> 1) (app todo t u @@ j) $
                  mapWithKey
                    (\alpha uAlpha ->
                      app todo (t `face` alpha) uAlpha @@ (Atom i :/\: Atom j)) us
        theta'  = compNeg j a theta ws
        xs      = insertSystem (i ~> 0) (app todo s v @@ j) $
                  insertSystem (i ~> 1) (app todo s (app todo f u) @@ j) $
                  mapWithKey
                    (\alpha uAlpha ->
                      app todo (s `face` alpha) (app todo (f `face` alpha) uAlpha) @@ j) us
        theta'' = comp j b (app todo f theta') xs


-------------------------------------------------------------------------------
-- | GlueLine


glueLine :: Val -> Formula -> Formula -> Val
glueLine t _ (Dir Zero)  = t
glueLine t (Dir _) _     = t
glueLine t phi (Dir One) = glue t isos
  where isos = mkSystem (map (\alpha -> (alpha,idIso (t `face` alpha)))
                         (invFormula phi Zero))
glueLine t phi psi       = VGlueLine t phi psi

idIso :: Val -> Val
idIso a = VPair a $ VPair idV $ VPair idV $ VPair refl refl
  where idV  = Ter (Lam "x" (Var "A") (Var "x")) (upd ("A",a) empty)
        refl = Ter (Lam "x" (Var "A") (Path (Name "i") (Var "x")))
                   (upd ("A",a) empty)

glueLineElem :: Val -> Formula -> Formula -> Val
glueLineElem u (Dir _) _     = u
glueLineElem u _ (Dir Zero)  = u
glueLineElem u phi (Dir One) = glueElem u ss
 where ss = mkSystem (map (\alpha -> (alpha,u `face` alpha))
                      (invFormula phi Zero))
glueLineElem u phi psi       = VGlueLineElem u phi psi

unGlueLine :: Val -> Formula -> Formula -> Val -> Val
unGlueLine b phi psi u = case (phi,psi,u) of
   (Dir _,_,_)    -> u
   (_,Dir Zero,_) -> u
   (_,Dir One,_)  ->
      let isos = mkSystem (map (\alpha -> (alpha,idIso (b `face` alpha)))
                            (invFormula phi Zero))
      in unGlue isos u
   (_,_,VGlueLineElem w _ _ ) -> w
   (_,_,_) -> error ("UnGlueLine, should be VGlueLineElem " ++ show u)

compGlueLine :: Name -> Val -> Formula -> Formula -> Val -> System Val -> Val
compGlueLine i b phi psi u us = glueLineElem vm phi psi
  where fs = invFormula psi One
        ws = mapWithKey
               (\alpha -> unGlueLine (b `face` alpha)
                            (phi `face` alpha) (psi `face` alpha)) us
        w  = unGlueLine b phi psi u
        v  = comp i b w ws

        lss = mkSystem $ map
                (\alpha ->
                  (alpha,(phi `face` alpha,b `face` alpha,
                          us `face` alpha,u `face` alpha))) fs
        ls = mapWithKey (\alpha vAlpha ->
                          auxGlueLine i vAlpha (v `face` alpha)) lss

        vm = compLine b v ls

auxGlueLine :: Name -> (Formula,Val,System Val,Val) -> Val -> Val
auxGlueLine i (Dir _,b,ws,wi0) vi1 = VPath j vi1 where j = fresh vi1
auxGlueLine i (phi,b,ws,wi0) vi1   = fillLine b vi1 ls'
  where hisos = mkSystem (map (\alpha ->
                  (alpha,idIso (b `face` alpha))) (invFormula phi Zero))
        vs  = mapWithKey (\alpha -> unGlue (hisos `face` alpha)) ws
        vi0 = unGlue hisos wi0 -- in b

        v   = fill i b vi0 vs  -- in b
        us' = mapWithKey (\gamma _ ->
                           fill i (b `face` gamma) (wi0 `face` gamma)
                             (ws `face` gamma))
                hisos

        ls' = mapWithKey (\gamma _ ->
                           pathComp i (b `face` gamma) (v `face` gamma)
                             (us' ! gamma) (vs `face` gamma))
                hisos

transGlueLine :: Name -> Val -> Formula -> Formula -> Val -> Val
transGlueLine i b phi psi u = glueLineElem vm phii1 psii1
  where fs = filter (i `Map.notMember`) (invFormula psi One)
        phii1   = phi `face` (i ~> 1)
        psii1   = psi `face` (i ~> 1)
        phii0   = phi `face` (i ~> 0)
        psii0   = psi `face` (i ~> 0)
        bi1 = b `face`  (i ~> 1)
        bi0 = b `face`  (i ~> 0)
        lss = mkSystem (map (\ alpha ->
                (alpha,(face phi alpha,face b alpha,face u alpha))) fs)
        ls = mapWithKey (\alpha vAlpha ->
               auxTransGlueLine i vAlpha (v `face` alpha)) lss
        v = trans i b w
        w  = unGlueLine bi0 phii0 psii0 u
        vm = compLine bi1 v ls

auxTransGlueLine :: Name -> (Formula,Val,Val) -> Val -> Val
auxTransGlueLine i (Dir _,b,wi0) vi1 = VPath j vi1 where j = fresh vi1
auxTransGlueLine i (phi,b,wi0) vi1   = fillLine (b `face` (i ~> 1)) vi1 ls'
  where hisos = mkSystem (map (\ alpha ->
                  (alpha,idIso (b `face` alpha))) (invFormula phi Zero))
        vi0  = unGlue (hisos `face` (i ~> 0)) wi0 -- in b(i0)
        v    = transFill i b vi0           -- in b

        -- set of elements in hisos independent of i
        hisos'  = filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos

        us' = mapWithKey (\gamma _ ->
                  transFill i (b `face` gamma) (wi0 `face` gamma))
                hisos'

        ls' = mapWithKey (\gamma _ ->
                  VPath i $ squeeze i (b `face` gamma) (us' ! gamma))
                hisos'



-------------------------------------------------------------------------------
-- | Composition in the Universe

isConstPath :: Val -> Bool
isConstPath (VPath i u) = i `notElem` support u
isConstPath _ = False

compElem :: Val -> System Val -> Val -> System Val -> Val
compElem a es u us = compElem' (Map.filter (not . isConstPath) es)
  where compElem' es | Map.null es         = u
                     | eps `Map.member` us = us ! eps
                     | otherwise           = VCompElem a es u us

elimComp :: Val -> System Val -> Val -> Val
elimComp a es u = elimComp' (Map.filter (not . isConstPath) es)
  where elimComp' es | Map.null es         = u
                     | eps `Map.member` es = transNegLine (es ! eps) u
                     | otherwise           = VElimComp a es u

compU :: Name -> Val -> System Val -> Val -> System Val -> Val
compU i a es w0 ws =
    let vs = mapWithKey
               (\alpha -> elimComp (a `face` alpha) (es `face` alpha)) ws
        v0 = elimComp a es w0 -- in a
        v1 = comp i a v0 vs -- in a

        us1' = mapWithKey (\gamma eGamma ->
                            comp i (eGamma @@ One) (w0 `face` gamma)
                                   (ws `face` gamma)) es
        ls' = mapWithKey
                (\gamma eGamma -> pathUniv i eGamma
                                  (ws `face` gamma) (w0 `face` gamma))
                es

        v1' = compLine a v1 ls'
    in compElem a es v1' us1'

-- Computes a homotopy between the image of the composition, and the
-- composition of the image. Given e (an equality in U), an L-system
-- us (in e0) and ui0 (in e0 (i0)) The output is an L(i1)-path in
-- e1(i1) between vi1 and sigma (i1) ui1 where
--   sigma = appEq
--   ui1 = comp i (e 0) us ui0
--   vi1 = comp i (e 1) (sigma us) (sigma(i0) ui0)
-- Moreover, if e is constant, so is the output.
pathUniv :: Name -> Val -> System Val -> Val -> Val
pathUniv i e us ui0 = VPath k xi1
  where j:k:_ = freshs (Atom i,e,us,ui0)
        ej    = e @@ j
        ui1   = comp i (e @@ One) ui0 us
        ws    = mapWithKey (\alpha uAlpha ->
                  transFillNeg j (ej `face` alpha) uAlpha)
                us
        wi0   = transFillNeg j (ej `face` (i ~> 0)) ui0
        wi1   = comp i ej wi0 ws
        wi1'  = transFillNeg j (ej `face` (i ~> 1)) ui1
        xi1   = genCompNeg j (ej `face` (i ~> 1)) ui1
                  (mkSystem [(k ~> 1, wi1'), (k ~> 0, wi1)])

transU :: Name -> Val -> System Val -> Val -> Val
transU i a es wi0 =
  let vi0 = elimComp (a `face` (i ~> 0)) (es `face` (i ~> 0)) wi0 -- in a(i0)
      vi1 = trans i a vi0      -- in a(i1)

      ai1  = a `face` (i ~> 1)
      esi1 = es `face` (i ~> 1)

      -- gamma in es'' iff i not in the domain of gamma and (i1)gamma in es
      es'' = filterWithKey (\alpha _ -> alpha `Map.notMember` es) esi1

      -- set of faces alpha of es such i is not the domain of alpha
      es'  = filterWithKey (\alpha _ -> i `Map.notMember` alpha) es

      usi1' = mapWithKey (\gamma eGamma ->
                trans i (eGamma @@ One) (wi0 `face` gamma)) es'

      ls' = mapWithKey (\gamma _ ->
              pathUnivTrans i (es `proj` gamma) (wi0 `face` gamma))
--                         pathUniv i (es `proj` gamma) Map.empty (wi0 `face` gamma))
            es'

      vi1' = compLine ai1 vi1 ls'

      uls'' = mapWithKey (\gamma _ -> -- Should be !, not proj ?
                eqLemma (es ! (gamma `meet` (i ~> 1)))
                        (usi1' `face` gamma) (vi1' `face` gamma)) es''

      vi1'' = compLine ai1 vi1' (Map.map snd uls'')

      usi1  = mapWithKey (\gamma _ ->
                if gamma `Map.member` usi1' then usi1' ! gamma
                else fst (uls'' ! gamma)) esi1
  in compElem ai1 esi1 vi1'' usi1


pathUnivTrans :: Name -> Val -> Val -> Val
pathUnivTrans i e ui0 = VPath j xi1
  where j    = fresh (Atom i,e,ui0)
        ej   = e @@ j
        wi0  = transFillNeg j (ej `face` (i ~> 0)) ui0
        wi1  = trans i ej wi0
        xi1  = squeezeNeg j (ej `face` (i ~> 1)) wi1

-- Any equality defines an equivalence.
eqLemma :: Val -> System Val -> Val -> (Val, Val)
eqLemma e ts a = (t,VPath j theta'')
  where i:j:_   = freshs (e,ts,a)
        ei      = e @@ i
        vs      = mapWithKey (\alpha uAlpha ->
                    transFillNeg i (ei `face` alpha) uAlpha) ts
        theta   = genFill i ei a vs
        t       = genComp i ei a vs
        theta'  = transFillNeg i ei t
        ws      = insertSystem (j ~> 1) theta' $ insertSystem (j ~> 0) theta vs
        theta'' = genCompNeg i ei t ws


-------------------------------------------------------------------------------

-- Addition?: (Name == Formula) constraints, to handle dimensions defined in the environment
type VarConstr  = [(Ident,Ident)]

abstractVC :: Ident -> Ident -> VarConstr -> Maybe VarConstr
abstractVC x y c = do
    guard $ all (== (x,y)) (zy ++ xz)
    return $ [ p | p@(a,b) <- c, a /= x]
  where
    zy = [ p |  p@(_,b) <- c, b == y ]
    xz = [ p |  p@(a,_) <- c, a == x ]

(<+>) :: (Monoid a, Monad m) => m a -> m a -> m a
m <+> n = liftM2 (<>) m n

class Alpha a where
  alpha :: a -> a -> Maybe VarConstr

instance Alpha a => Alpha [a] where
  alpha ts ts' = foldr (<+>) (return mempty) (zipWith alpha ts ts')

instance Alpha Formula where
  alpha phi phi' = guard (conv [] phi phi') >> return mempty -- TODO: handle defined names

instance Alpha a => Alpha (System a) where
  alpha ts ts' = do
     guard (keys ts == keys ts') -- TODO: handle defined names
     foldr (<+>) (return mempty) (elems (intersectionWith alpha ts ts'))

instance (Alpha a, Alpha b, Alpha c) => Alpha (a,b,c) where
  alpha (a,b,c) (a',b',c') = alpha a a' <+> alpha b b' <+> alpha c c'

instance (Alpha a, Alpha b) => Alpha (a,b) where
  alpha (a,b) (a',b') = alpha a a' <+> alpha b b'

instance Alpha Ter where
  alpha t t' = case (t,t') of
    ( App t u, App t' u') -> alpha t t' <+> alpha u u'
    ( Pi t, Pi t')        -> alpha t t'
    ( Lam x a t, Lam x' a' t') -> abstractVC x x' =<< alpha t t'
    ( Where t ds, Where t' ds') -> Nothing -- TODO
    ( Var x, Var y)       -> return $ [(x,y)]
    ( U, U)               -> return mempty
             -- Sigma types:
    ( Sigma t, Sigma t') -> alpha t t'
    ( Pair t u, Pair t' u') -> alpha t t' <+> alpha u u'
    ( Fst t, Fst t') -> alpha t t'
    ( Snd t, Snd t') -> alpha t t'
             -- constructor c Ms
    ( Con l ts, Con l' ts') -> guard (l == l') >> alpha ts ts'
    ( PCon l t ts phis, PCon l' t' ts' phis') -> guard (l == l') >> (alpha t t' <+> alpha ts ts' <+> alpha phis phis')
                -- c A ts phis (A is the data type)
             -- branches c1 xs1  -> M1,..., cn xsn -> Mn
    ( Split _ p _ _, Split _ p' _ _) -> guard (p == p') >> return mempty
             -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
    ( Sum p _ _, Sum p' _ _) -> guard (p == p') >> return mempty

             -- undefined and holes
    ( Undef p _, Undef p' _) -> guard (p == p') >> return mempty
    ( Hole p, Hole p')       -> guard (p == p') >> return mempty

    ( IdP a t u, IdP a' t' u') -> alpha (a,t,u) (a',t',u')
    ( Path i t, Path i' t')
            -> let j = fresh (t,t') in alpha (t `swap` (i,j)) (t' `swap` (i',j))
    ( AppFormula t phi, AppFormula t' phi') -> alpha (t,phi) (t',phi')
             -- Kan Composition
    ( Comp a t ts, Comp a' t' ts') -> alpha (a,t,ts) (a',t',ts')
    ( Trans a t, Trans a' t')      -> alpha (a,t) (a',t')
             -- Composition in the Universe
    ( CompElem t ts u us, CompElem t' ts' u' us') -> alpha t t' <+> alpha (ts,u,us) (ts',u',us')
    ( ElimComp t ts u, ElimComp t' ts' u') -> alpha (t,ts,u) (t',ts',u')
             -- Glue
    ( Glue t ts, Glue t' ts') -> alpha (t,ts) (t',ts')
    ( GlueElem t ts, GlueElem t' ts') -> alpha (t,ts) (t',ts')
             -- GlueLine: connecting any type to its glue with identities
    ( GlueLine t phi psi, GlueLine t' phi' psi') -> alpha (t,phi,psi) (t',phi',psi')
    ( GlueLineElem t phi psi, GlueLineElem t' phi' psi') -> alpha (t,phi,psi) (t',phi',psi')

             -- guarded recursive types
    ( Later xi t, Later xi' t') -> do c <- alpha t t'; alphaDelSubst c xi xi'
    ( Next xi t, Next xi' t')   -> do c <- alpha t t'; alphaDelSubst c xi xi'
    ( Fix _ t, Fix _ t')        -> alpha t t'
    _ -> trace ("alpha:\n" ++ show t ++ "\nvs.\n" ++ show t') $ Nothing

alphaDelSubst :: VarConstr -> DelSubst -> DelSubst -> Maybe VarConstr
alphaDelSubst c xi xi' = foldr (<+>) (return mempty) [ alpha (lookDS' x xi) (lookDS' y xi')  | (x,y) <- c ]
  where
   lookDS' x xi = maybe (Next [] (Var x)) id (lookDS x xi)

convEnv :: [String] -> VarConstr -> Env -> Env -> Bool
convEnv ns c rho rho' = and [ conv ns (lookDel x rho) (lookDel y rho') | (x,y) <- c ]

-- | Conversion

class Convertible a where
  conv :: [String] -> a -> a -> Bool

isIndep :: (Nominal a, Convertible a) => [String] -> Name -> a -> Bool
isIndep ns i u = conv ns u (u `face` (i ~> 0))

isCompSystem :: (Nominal a, Convertible a) => [String] -> System a -> Bool
isCompSystem ns ts = and [ conv ns (getFace alpha beta) (getFace beta alpha)
                         | (alpha,beta) <- allCompatible (keys ts) ]
    where getFace a b = face (ts ! a) (b `minus` a)

simplify :: [String] -> Name -> Val -> Val
simplify ns j v = case v of
  VTrans p u | isIndep ns j (p @@ j) -> simplify ns j u
  VComp a u ts ->
    let (indep,ts') = Map.partition (\t -> isIndep ns j (t @@ j)) ts
    in if Map.null ts' then simplify ns j u else VComp a u ts'
  VCompElem a es u us ->
    let (indep,es') = Map.partition (\e -> isIndep ns j (e @@ j)) es
        us'         = intersection us es'
    in if Map.null es' then simplify ns j u else VCompElem a es' u us'
  VElimComp a es u ->
    let (indep,es') = Map.partition (\e -> isIndep ns j (e @@ j)) es
        u'          = simplify ns j u
    in if Map.null es' then u' else case u' of
      VCompElem _ _ w _ -> simplify ns j w
      _ -> VElimComp a es' u'
  _ -> v

instance Convertible Val where
  conv ns u v | u == v    = True
              | otherwise =
    let j = fresh (u,v)
    in trace ("conv:\n" ++ show u ++ "\nvs.\n" ++ show v) $ case (simplify ns j u, simplify ns j v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (eval (upd (x',v) e') u')
      (Ter (Lam x a u) e,u') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (app todo u' v)
      (u',Ter (Lam x a u) e) ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (app todo u' v) (eval (upd (x,v) e) u)
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> (p == p') && conv ns e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')         -> (p == p') && conv ns e e'
      (Ter (Undef p _) e,Ter (Undef p' _) e') -> p == p' && conv ns e e'
      (Ter (Hole p) e,Ter (Hole p') e') -> p == p' && conv ns e e'
      -- (Ter Hole{} e,_) -> True
      -- (_,Ter Hole{} e') -> True
      (VPi u v,VPi u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app todo v w) (app todo v' w)
      (VSigma u v,VSigma u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app todo v w) (app todo v' w)
      (VCon c us,VCon c' us')   -> (c == c') && conv ns us us'
      (VPCon c v us phis,VPCon c' v' us' phis') ->
        (c == c') && conv ns (v,us,phis) (v',us',phis')
      (VPair u v,VPair u' v')    -> conv ns u u' && conv ns v v'
      (VPair u v,w)              -> conv ns u (fstVal w) && conv ns v (sndVal w)
      (w,VPair u v)              -> conv ns (fstVal w) u && conv ns (sndVal w) v
      (VFst u,VFst u')           -> conv ns u u'
      (VSnd u,VSnd u')           -> conv ns u u'
      (VApp u v,VApp u' v')      -> conv ns u u' && conv ns v v'
      (VSplit u v,VSplit u' v')  -> conv ns u u' && conv ns v v'
      (VVar x _, VVar x' _)      -> x == x'
      (VIdP a b c,VIdP a' b' c') -> conv ns a a' && conv ns b b' && conv ns c c'
      (VPath i a,VPath i' a')    -> conv ns (a `swap` (i,j)) (a' `swap` (i',j))
      (VPath i a,p')             -> conv ns (a `swap` (i,j)) (p' @@ j)
      (p,VPath i' a')            -> conv ns (p @@ j) (a' `swap` (i',j))
      (VTrans p u,VTrans p' u')  -> conv ns p p' && conv ns u u'
      (VAppFormula u x,VAppFormula u' x') -> conv ns (u,x) (u',x')
      (VComp a u ts,VComp a' u' ts') -> conv ns (a,u,ts) (a',u',ts')
      (VGlue v hisos,VGlue v' hisos') -> conv ns (v,hisos) (v',hisos')
      (VGlueElem u us,VGlueElem u' us') -> conv ns (u,us) (u',us')
      (VCompElem a es u us,VCompElem a' es' u' us') ->
        conv ns (a,es,u,us) (a',es',u',us')
      (VElimComp a es u,VElimComp a' es' u') -> conv ns (a,es,u) (a',es',u')
      (Ter (Var i) e,Ter (Var i') e') -> conv ns (lookDel i e) (lookDel i' e')
      (VLater v,VLater v') -> conv ns v v'
      (VNext v,VNext v') -> conv ns v v'
      (VFix va vf, VFix va' vf') -> conv ns (va,vf) (va',vf')
      (Ter t@(Fix _ _) e, v) -> conv ns (eval e t) v
      (v,Ter t@(Fix _ _) e) -> conv ns v (eval e t)

      -- (VLater (Ter t rho), VLater (Ter t' rho')) -> maybe False (\ c -> convEnv ns c rho rho') (alpha t t')
      -- (VLater v, VLater (Ter t' rho')) -> maybe False (\ c -> convEnv ns c rho rho') (alpha t t')
      -- (VNext (Ter t rho), VNext (Ter t' rho')) -> maybe False (\ c -> convEnv ns c rho rho') (alpha t t')
      -- (VNext v, u) -> let x = "$x" in alpha ns Map.empty Map.empty v (Ter (Var x) (delUpd (x,u) empty))
      -- (u, VNext v) -> let x = "$x" in alpha ns Map.empty Map.empty v (Ter (Var x) (delUpd (x,u) empty))
      _                         -> False


getDelVals :: DelSubst -> [(Ident,Ter)]
getDelVals ds = map (\ (DelBind (f,(a,t))) -> (f,t)) ds

freshVar :: Env -> Ident
freshVar e = gensymV (envVars e)

gensymV :: [Ident] -> Ident
gensymV xs = ('$' : show max)
  where max = maximum' [ read x | ('$':x) <- xs ]
        maximum' [] = 0
        maximum' xs = maximum xs + 1

envVars :: Env -> [Ident]
envVars (c,_,_,_) = go c
  where
    go c = case c of
      Empty -> []
      Sub _ c -> go c
      Upd i c -> i : go c
      DelUpd i c -> i : go c

instance Convertible Ctxt where
  conv _ _ _ = True

instance Convertible () where
  conv _ _ _ = True

-- instance Convertible Char where
--   conv _ = (==)

-- instance (Ord k, Convertible a) => Convertible (Map k a) where
--   conv ns f g = keys f == keys g &&
--                 and (elems (intersectionWith (conv ns) f g))

instance Convertible (Map Ident Val) where
  -- we want this to be antisymmetric: f \subseteq g
  -- f <= g <=> f == (f /\ g)
  conv ns f g = keys f == keys (f `Map.intersection` g) &&
                and (elems (intersectionWith (conv ns) f g))


instance (Convertible a, Convertible b) => Convertible (Either a b) where
  conv ns (Left v) (Left v')   = conv ns v v'
  conv ns (Right v) (Right v') = conv ns v v'
  conv _  _ _                  = False

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv ns (u, v) (u', v') = conv ns u u' && conv ns v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv ns (u, v, w) (u', v', w') = conv ns (u,(v,w)) (u',(v',w'))

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv ns (u,v,w,x) (u',v',w',x') = conv ns (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv ns us us' = length us == length us' &&
                  and [conv ns u u' | (u,u') <- zip us us']

instance Convertible a => Convertible (System a) where
  conv ns ts ts' = keys ts == keys ts' &&
                   and (elems (intersectionWith (conv ns) ts ts'))

instance Convertible Formula where
  conv _ phi psi = dnf phi == dnf psi

-------------------------------------------------------------------------------
-- | Normalization

class Normal a where
  normal :: [String] -> a -> a

-- Does neither normalize formulas nor environments.
instance Normal Val where
  normal ns v = case v of
    VU                  -> VU
    Ter (Lam x t u) e   -> let w = eval e t
                               v@(VVar n _) = mkVarNice ns x w
                           in VLam n (normal ns w) $ normal (n:ns) (eval (upd (x,v) e) u)
    Ter t e             -> Ter t (normal ns e)
    VPi u v             -> VPi (normal ns u) (normal ns v)
    VSigma u v          -> VSigma (normal ns u) (normal ns v)
    VPair u v           -> VPair (normal ns u) (normal ns v)
    VCon n us           -> VCon n (normal ns us)
    VPCon n u us phis   -> VPCon n (normal ns u) (normal ns us) phis
    VIdP a u0 u1        -> VIdP (normal ns a) (normal ns u0) (normal ns u1)
    VPath i u           -> VPath i (normal ns u)
    VComp u v vs        -> compLine (normal ns u) (normal ns v) (normal ns vs)
    VTrans u v          -> transLine (normal ns u) (normal ns v)
    VGlue u hisos       -> glue (normal ns u) (normal ns hisos)
    VGlueElem u us      -> glueElem (normal ns u) (normal ns us)
    VCompElem a es u us -> compElem (normal ns a) (normal ns es) (normal ns u) (normal ns us)
    VElimComp a es u    -> elimComp (normal ns a) (normal ns es) (normal ns u)
    VVar x t            -> VVar x t -- (normal ns t)
    VFst t              -> fstVal (normal ns t)
    VSnd t              -> sndVal (normal ns t)
    VSplit u t          -> VSplit (normal ns u) (normal ns t)
    VApp u v            -> app todo (normal ns u) (normal ns v)
    VAppFormula u phi   -> VAppFormula (normal ns u) (normal ns phi)
    VNext v             -> VNext (normal ns v)
    VLater v            -> VLater (normal ns v)
    _                   -> v

instance Normal Ctxt where
  normal _ = id

instance Normal Formula where
  normal _ = fromDNF . dnf

instance Normal a => Normal (Map k a) where
  normal ns = Map.map (normal ns)

instance (Normal a,Normal b) => Normal (a,b) where
  normal ns (u,v) = (normal ns u,normal ns v)

instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal ns (u,v,w) = (normal ns u,normal ns v,normal ns w)

instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal ns (u,v,w,x) =
    (normal ns u,normal ns v,normal ns w, normal ns x)

instance Normal a => Normal [a] where
  normal ns = map (normal ns)
