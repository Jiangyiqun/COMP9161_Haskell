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
           |  F VEnv [Char] [[Char]] Exp
           |  Func Bind
           -- Others as needed
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
evalE env (App (App (Con "Cons") x) xs) = 
    let I vx = evalE env x
        vxs = evalE env xs
    in Cons vx vxs

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
-- data Bind = Bind Id Type [Id] Exp
evalE env (Let ((Bind id _ [] e1) : x) e2) =
    let v1 = evalE env e1
        v2 = evalE (E.add env (id, v1)) (Let x e2)
    in v2

-- Evaluation of if-expression
evalE env (If e1 e2 e3) =
    case evalE env e1 of
      (B True) -> evalE env e2
      (B False) -> evalE env e3
evalE env exp = error "error: unknown"
