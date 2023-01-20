module Main

import public Multiplate
import Control.Monad.State
import Control.Applicative.Const
import Data.List
import Data.Maybe

mutual
    data Expr
        = Add Expr Expr
        | Sub Expr Expr
        | Lit Integer
        | Var String
        | Block (List Stmt) Expr

    data Stmt
        = Let String Expr
        | Return Expr

record ExprPlate f where
    constructor MkExprPlate
    expr : Expr -> f Expr
    stmt : Stmt -> f Stmt

Multiplate ExprPlate where
    multiplate p = MkExprPlate
        (\case
            Add l r => Add <$> p.expr l <*> p.expr r
            Sub l r => Sub <$> p.expr l <*> p.expr r
            Lit x => pure $ Lit x
            Var v => pure $ Var v
            Block xs e => Block <$> traverse p.stmt xs <*> p.expr e)
        (\case
            Let var val => Let var <$> p.expr val
            Return e => Return <$> p.expr e)
    mkPlate build = MkExprPlate (build expr) (build stmt)

HasField ExprPlate Expr where
    project = expr
    update f p = { expr := f } p

HasField ExprPlate Stmt where
    project = stmt
    update f p = { stmt := f } p

exampleExpr : Expr
exampleExpr = Add (Add (Lit 10) (Lit 22)) (Sub (Lit 8) (Lit 2))

constFold : ExprPlate Identity
constFold = inject $ \case
    Add (Lit x) (Lit y) => pure $ Lit (x + y)
    Sub (Lit x) (Lit y) => pure $ Lit (x - y)
    x => pure x

covering
doGetLetBound : ExprPlate (Const (List String))
doGetLetBound = preorderFold $ inject $ \case
    Let f _ => MkConst [f]
    _ => neutral

covering
getLetBound : HasField ExprPlate a => a -> List String
getLetBound = foldFor doGetLetBound

filterM : Applicative f => (a -> f Bool) -> List a -> f (List a)
filterM pred [] = pure []
filterM pred (x :: xs) = go <$> pred x <*> filterM pred xs
  where
    go : Bool -> List a -> List a
    go True xs = x :: xs
    go False xs = xs

-- note: this doesn't deal with scoping
inlineLet : ExprPlate (State (List (String, Expr)))
inlineLet = MkExprPlate
    { stmt = \case
        x@(Let var val) => x <$ modify ((var, val) ::) -- add the defintion to the environment
        x => pure x
    , expr = \case
        Var v => do -- replace variables with their definitions
            Just val <- gets $ lookup v
                | Nothing => pure $ Var v
            pure val
        Block xs e => Block <$> filterM (\case -- remove lets which have been added to the environment
            Let v _ => gets $ isNothing . lookup v
            _ => pure True) xs <*> pure e
        x => pure x
    }

removeEmptyBlock : ExprPlate Identity
removeEmptyBlock = inject $ \case
    Block [] e => pure e
    x => pure x

longExample : Expr
longExample = Block
    [ Let "foo" (Lit 10)
    , Let "bah" (Add (Var "foo") (Var "foo"))
    ]
    (Sub (Var "bah") (Var "foo"))

covering
doInlineLet : HasField ExprPlate a => a -> a
doInlineLet = evalState [] . project
    (mapFamily $ inlineLet
        `andThenId` removeEmptyBlock)

covering
doEverything : HasField ExprPlate a => a -> a
doEverything = evalState [] . project
    (mapFamily $ inlineLet
        `andThenId` removeEmptyBlock
        `andThenId` constFold)

main : IO ()
main = putStrLn "Tests passed"
