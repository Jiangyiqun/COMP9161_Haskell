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
evalE env (Con "True") = B True
evalE env (Con "False") = B False
evalE env (Num v) = I v


-- List constructors and primops
evalE env (Con "Nil") = Nil
evalE env (App (App (Con "Cons") e1) e2) = 
    let I v1 = evalE env e1
        v2 = evalE env e2
    in Cons v1 v2


evalE env (App (Prim Head) x) =
    case evalE env x of
    Nil      -> error "error: empty list does not have head"
    Cons v vs -> I v

evalE env (App (Prim Tail) x) =
    case evalE env x of
    Nil       -> error "error: empty list does not have tail"
    Cons v vs -> vs

evalE env (App (Prim Null) x) =
    case evalE env x of
    Nil      -> B True
    Cons _ _ -> B False


-- Primitive operations
evalE env (App (App (Prim op) e1) e2) = 
    let I v1 = evalE env e1
        I v2 = evalE env e2
    in case op of
        Add   -> I (v1 + v2)
        Sub   -> I (v1 - v2)
        Mul   -> I (v1 * v2)
        Quot  -> case v2 of
                  0 -> error "error: divide by zero"
                  _ -> I (quot v1 v2)
        Gt    -> B (v1 > v2)
        Ge    -> B (v1 >= v2)
        Lt    -> B (v1 < v2)
        Le    -> B (v1 <= v2)
        Eq    -> B (v1 == v2)
        Ne    -> B (v1 /= v2)

evalE env (App (Prim Neg) e) =
    let I v = evalE env e 
    in I (-v)


-- Variables
evalE env (Var x) = case E.lookup env x of
    Just v -> v
    Nothing -> error ("error: Nothing")


-- Variable Bindings with Let
evalE env (Let [] e) = evalE env e
evalE env (Let ((Bind id _ [] e1) : x) e2) =
    let v1 = evalE env e1
        v2 = evalE (E.add env (id, v1)) (Let x e2)
    in v2


-- Evaluation of if-expression
evalE env (If e1 e2 e3) =
    case evalE env e1 of
      (B True) -> evalE env e2
      (B False) -> evalE env e3


-- Function values
evalE env (Recfun (Bind f _ x e)) =
    let env' = E.add env (f, (Closure env f x e))
    in Closure env' f x e


-- Function Application
evalE env (App e1 e2) = 
    let Closure env' f x e = evalE env e1    -- evaluate e1
        env1 = E.add env' (f, Closure env' f x e)
        env2 = E.add env1 (head x, evalE env e2) -- evaluate e2
        r = evalE env2 e
    in r


-- Other
evalE env e = error "error: other"
