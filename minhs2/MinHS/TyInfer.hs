module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)


------------------------------ Unification -----------------------------
unify :: Type -> Type -> TC Subst

unify (TypeVar v1) (TypeVar v2) =
  case v1 == v2 of True -> return emptySubst
                   False -> return (v1 =: (TypeVar v2))
                  
unify (Base t1) (Base t2) =
  case t1 == t2 of True -> return emptySubst
                   False -> typeError (TypeMismatch (Base t1) (Base t2))

unify (Prod x1 x2) (Prod y1 y2) =
  unify x1 y1 >>= (
    \s1 -> unify (substitute s1 x2) (substitute s1 y2) >>= (
      \s2 -> return (s1 <> s2)))

unify (Sum x1 x2) (Sum y1 y2) =
  unify x1 y1 >>= (
    \s1 -> unify (substitute s1 x2) (substitute s1 y2) >>= (
      \s2 -> return (s1 <> s2)))

unify (Arrow x1 x2) (Arrow y1 y2) =
  unify x1 y1 >>= (
    \s1 -> unify (substitute s1 x2) (substitute s1 y2) >>= (
      \s2 -> return (s1 <> s2)))

unify (TypeVar v) (t) =
  case (elem v (tv t)) of True -> typeError (OccursCheckFailed v t)
                          False -> return (v =: t) 

unify (t) (TypeVar v) =
  case (elem v (tv t)) of True -> typeError (OccursCheckFailed v t)
                          False -> return (v =: t)

unify t1 t2 = error ("something went wrong in unify!")


----------------------------- Generalise ------------------------------
generalise :: Gamma -> Type -> QType
{-
foldl  	(a -> b -> a) -> a -> [b] -> a
it takes the second argument and the first item of the list and applies
the function to them, then feeds the function with this result and the
second argument and so on. 
-}  
generalise g t = 
  let f = \t' -> \x -> Forall x t'
      arg = Ty t
      list = let f' = \x -> not $ elem x (tvGamma g)
                 exp = tv t
              in reverse (filter f' exp)
   in foldl f arg list

convertToTc::Gamma -> Type -> TC QType
convertToTc g t = do
  return (generalise g t)


-- ------------------------------ Infer Program ---------------------------
-- inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram g [Bind id Nothing [] e] = 
    inferExp g e >>= \(expr', t , s) -> 
      let program = ([Bind id (Just (generalise g t)) [] (allTypes (substQType s) expr') ])
       in return (program, t, s)


--------------------------- Type Inference Rule ------------------------                            
inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)

-- Constants and Varibles
inferExp g (Num n) =
  return (Num n, Base Int, emptySubst)

inferExp g (Var id) = 
  let Just qtau = E.lookup g id
  in unquantify (qtau) >>= (
    \t -> return (Var id, t, emptySubst)) 

-- Constructors and Primops
inferExp g (Con c) =
  let Just qtau = constType c
  in unquantify (qtau) >>= (
    \t -> return (Con c, t, emptySubst))

inferExp g (Prim p) =
  let qtau = primOpType p
  in unquantify (qtau) >>= (
    \t -> return (Prim p, t, emptySubst))

-- Applications
inferExp g (App e1 e2) =
  inferExp g e1 >>= (
  \(e1', t1, s1) -> inferExp g e2 >>= (
  \(e2', t2, s2) -> fresh >>= (
  \alpha -> unify (substitute s2 t1) (Arrow t2 alpha) >>= (
  \u -> let e'' = App e1' e2'
            e1'' = substitute u alpha
            e2'' = s1<>s2<>u
         in return (e'', e1'', e2'')
  ))))

-- If Statement 
inferExp g (If e e1 e2) =
  inferExp g e >>= (
  \(e', t, s) -> unify t (Base Bool) >>= (
  \u -> inferExp g e1 >>= (
  \(e1', t1, s1) -> inferExp g e2 >>= (
  \(e2', t2, s2) -> unify (substitute s2 t1) (t2) >>= (
  \u' -> let e'' = If e' e1' e2'
             e1'' = substitute u' t2
             e2'' = u' <> s2 <> s1 <> u <> s
          in return(e'', e1'', e2'')
  )))))

-- Case
inferExp env (Case e [Alt id1 [x1] e1, Alt id2 [y1] e2]) =
  fresh >>= (
  \alpha1 -> fresh >>= (
  \alpha2 -> inferExp env e >>= (
  \(e', t, s) -> inferExp (E.add env (x1, (Ty alpha1))) e1 >>= (
  \(e1', tl, s1) -> inferExp (E.add env (y1, (Ty alpha2))) e2 >>= (
  \(e2', tr, s2) -> let t1 = substitute (s<>s1<>s2) (Sum alpha1 alpha2)
                        t2 = substitute (s1<>s2) t
                     in unify t1 t2 >>= (
  \u -> unify (substitute (s2<>u) tl) (substitute u tr) >>= (
  \u' -> let e'' = (Case e' [Alt id1 [x1] e1', Alt id2 [y1] e2'])
             x'' = substitute (u<>u') tr
             e1'' = u<>u'
          in return (e'' ,x'', e1'')
  )))))))

-- Recursive Functions
inferExp env (Recfun (Bind funId Nothing [varId] e)) =
  fresh >>= (
  \alpha1 -> fresh >>= (
  \alpha2 -> let env' = E.addAll env [(varId, (Ty alpha1)), (funId, (Ty alpha2))]
             in inferExp env' e >>= (
  \(e', t, s) -> unify (substitute s alpha2) (Arrow (substitute s alpha1) t) >>= (
  \u -> let gamma' = E.addAll env [(varId, (Ty alpha1)),(funId, (Ty alpha2))]
            type' = substitute u (Arrow (substitute s alpha1) t)
         in convertToTc gamma' type' >>= (
  \tf -> let f = (Recfun (Bind funId (Just tf) [varId] e'))
             x = (substitute u (Arrow (substitute s alpha1) t))
             e = s<>u
          in return (f, x , e)
  )))))

-- Let Bindings
inferExp env (Let [Bind id Nothing [] e1] e2) =
  inferExp env e1 >>= (
  \(e1', t1, s1) -> inferExp (E.add env (id, (generalise env t1))) e2 >>= (
  \(e2', t2, s2) -> convertToTc (E.add env (id, (generalise env t1))) t1 >>= (
  \t1Final -> let e1'' = (Let [Bind id (Just (t1Final)) [] e1'] e2')
                  x'' = t2
                  e2'' = s2<>s1
               in return (e1'', x'', e2'')
  )))

inferExp g _ = error "something wrong in inferExp!"