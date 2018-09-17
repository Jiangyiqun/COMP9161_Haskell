module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type VEnv = E.Env Value

data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           -- Others as needed
           | Closure VEnv [Char] [[Char]] Exp -- env f x e
           deriving (Show)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)
  pretty _ = undefined -- should not ever be used

evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE E.empty e
evaluate bs = evalE E.empty (Let bs (Var "main"))


evalE :: VEnv -> Exp -> Value


-- Constants and Boolean Constructors
evalE env (Num n)       = I n
evalE env (Con b)  = 
    case b of
        "True" -> B True
        "False" -> B False
        -- List constructors and primops
        "Nil" -> Nil    


-- Primitive operations
evalE env (App (App (Prim op) e1) e2) =
    let I v1 = evalE env e1
        I v2 = evalE env e2
    in  if op == Add
            then I (v1 + v2)
        else if op == Sub
            then I (v1 - v2)
        else if op == Mul
            then I (v1 * v2)
        else if op == Quot
            then if v2 == 0
                then error "error: divide by zero"
                else I (quot v1 v2)
        else if op == Gt
            then B (v1 >  v2)
        else if op == Ge
            then B (v1 >= v2)
        else if op == Lt
            then B (v1 <  v2)
        else if op == Le
            then B (v1 <= v2)
        else if op == Eq
            then B (v1 == v2)
        else if op == Ne
            then B (v1 /= v2)
        else
            error "error: operator does not support"
-- negation
-- evalE env (App (Prim Neg) e) =
--     let I v = evalE env e
--     in I (-v)


-- Evaluation of if-expression
evalE env (If e1 e2 e3) =
    let v1 = evalE env e1
    in case v1 of
        B True -> evalE env e2
        B False -> evalE env e3


-- Variables
evalE env (Var x) = case E.lookup env x of
    Just v -> v
    Nothing -> Nil


-- List constructors and primops
evalE env (App (App (Con "Cons") e1) e2) =
    let I v1 = evalE env e1
        v2 = evalE env e2
    in Cons v1 v2


-- evalE env (App (Prim Head) x) =
--     case evalE env x of
--     Nil      -> error "error: empty list does not have head"
--     Cons v vs -> I v
-- evalE env (App (Prim Tail) x) =
--     case evalE env x of
--     Nil       -> error "error: empty list does not have tail"
--     Cons v vs -> vs
-- evalE env (App (Prim Null) x) =
--     case evalE env x of
--     Nil      -> B True
--     Cons _ _ -> B False


-- Operator
evalE env (App (Prim op) e) =
    case op of
        -- List constructors and primops
        Head  -> case evalE env e of
                    Nil      -> error "error: empty list no head"
                    Cons v vs -> I v
        Tail  -> case evalE env e of
                    Nil       -> error "error: empty list no tail"
                    Cons v vs -> vs
        Null  -> case evalE env e of
                    Nil      -> B True
                    Cons _ _ -> B False
        -- nagation
        Neg   -> let I v = evalE env e
                 in I (-v)
        -- Partial Primops
        other -> let I v = evalE env e
                     exp = (App (App (Prim other) (Var "")) (Num v))
                 in Closure env "" [""] exp


-- Let Bindings
evalE env (Let [] e) = evalE env e
evalE env (Let ((Bind id _ args e1) : x) e2) =
    case args of
        -- Varible Bindings with Let
        [] -> let v1 = evalE env e1
                  v2 = evalE (E.add env (id, v1)) (Let x e2)
              in v2
        -- let bindings declare functions
        _  -> let v1 = Closure env id args e1
                  v2 = evalE (E.add env (id, v1)) (Let x e2)
              in v2


-- Function values
evalE env (Recfun (Bind id _ x e)) =
    let elt = Closure env id x e
        env' = E.add env (id, elt)
        v = Closure env' id x e
    in v


-- Function Application
evalE env (App (Var var) e2) =
    case (E.lookup env var) of
        Just (Closure env' f x e)  ->
            getReturn env (Closure env' f x e) e2
        Nothing                    -> error ("error: Nothing")
evalE env (App e1 e2) =
    let Closure env' f x e = evalE env e1    -- evaluate e1
        env1 = E.add env' (f, Closure env' f x e)
        env2 = E.add env1 (head x, evalE env e2) -- evaluate e2
    in case tail x of
        [] -> evalE env2 e
        _  -> (Closure env2 f (tail x) e)


-- Mutually recursive bindings
evalE env (Letrec e1 e2) =
    case e1 of
        [] -> evalE env e2      -- evaluate e2
        (Bind id ty [] e1):x
            -> let v1 = evalE env e1
               in case v1 of
                    Nil -> let e1' = Letrec (x ++ [Bind id ty [] e1])
                           in evalE env (e1' e2)
                    elt -> let env' = E.add env (id, elt)
                               v2 = Letrec x e2
                           in evalE env' v2


-- Other
evalE env e = error "error: other"


-- Partial Primops helper function
getReturn :: VEnv -> Value -> Exp -> Value
getReturn env (Closure env' f x e1) e2 =
    case x of
        [] -> let env1 = E.add env' (f, Closure env' f [] e1)
                  Closure env2 f' x' e' = evalE env1 e1
              in getReturn env (Closure env2 f' x' e') e2
        _  -> let env1 = E.add env' (f, Closure env' f x e1)
                  env2 = E.add env1 (head x, evalE env e2)
              in case tail x of
                  [] -> evalE env2 e1
                  _  -> (Closure env2 f (tail x) e1)