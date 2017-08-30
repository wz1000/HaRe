module M1 where
import Data.Char

data Expr = Var Char
          | N Int
          | Add Expr Expr
          | Sub Expr Expr
          | Assign Char Expr
          deriving Show

type Env = [(Char,Int)]

eval :: Expr -> Env -> (Int,Env)

eval (Var v) env = (head [val | (x,val) <- env, x==v], env)

eval (N n) env = (n,env)

eval (Add e1 e2) env = let (v1,env1) = eval e1 env
                           (v2,env2) = eval e2 env1 in
  (v1+v2,env2)
eval (Sub e1 e2) env = let (v1,env1) = eval e1 env
                           (v2,env2) = eval e2 env1 in
  (v1-v2,env2)
eval (Assign x e) env = let (v,env1) = eval e env in
  (v, (x,v):env1)
