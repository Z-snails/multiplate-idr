||| This example uses De Bruijn indexes for variables
||| to show how multiplate works with indexed data-types.
module Multiplate.Tests.DeBruijn

import Control.Monad.Identity

import Multiplate

data Var : List String -> Type where
    First : Var (v :: vs)
    Later : Var vs -> Var (v :: vs)

data Expr : List String -> Type where
    V : Var vs -> Expr vs
    Lam : (v : _) -> Expr (v :: vs) -> Expr vs
    App : Expr vs -> Expr vs -> Expr vs

||| The index can be erased
record ExprPlate f where
    constructor MkExprPlate
    expr : forall vs. Expr vs -> f (Expr vs)

||| Or it can be relevant
record UrExprPlate f where
    constructor MkUrExprPlate
    expr : {vs : _} -> Expr vs -> f (Expr vs)

Multiplate ExprPlate where
    multiplate p = MkExprPlate $ \case
        V v => pure $ V v
        Lam v e => Lam v <$> p.expr e
        App f x => App <$> p.expr f <*> p.expr x

    mkPlate build = MkExprPlate (build (\p => p.expr))

HasProjection ExprPlate (Expr vs) where
    project p = p.expr

Multiplate UrExprPlate where
    multiplate p = MkUrExprPlate $ \case
        V v => pure $ V v
        Lam v e => Lam v <$> p.expr e
        App f x => App <$> p.expr f <*> p.expr x

    mkPlate build = MkUrExprPlate (build (\p => p.expr))

{vs : _} -> HasProjection UrExprPlate (Expr vs) where
    project p = p.expr

data LengthOf : List String -> Type where
    Z : LengthOf []
    S : LengthOf xs -> LengthOf (x :: xs)

substVar :
    {0 outer : List String} ->
    {0 inner : List String} ->
    {auto len : LengthOf inner} ->
    Var (inner ++ [v] ++ outer) ->
    Expr outer ->
    Var (inner ++ [v] ++ outer) ->
    Expr (inner ++ outer)

subst :
    {0 outer : List String} ->
    {0 inner : List String} ->
    {auto len : LengthOf inner} ->
    Var (inner ++ [v] ++ outer) ->
    Expr outer ->
    Expr (inner ++ [v] ++ outer) ->
    Expr (inner ++ outer)
subst var val (V x) = substVar var val x
subst var val (Lam str x) = Lam str (subst {inner = str :: inner} (Later var) val x)
subst var val (App f x) = App (subst {inner} var val f) (subst {inner} var val x)

betaReduce : ExprPlate Identity
betaReduce = MkExprPlate $ \case
    App (Lam v e) x => pure $ subst {inner = []} First x e
    x => pure x

doBetaReduce : Expr vs -> Expr vs
doBetaReduce = traverseFor $ postorderMap betaReduce

example : Expr []
example = App (Lam "foo" (V First)) (Lam "bah" (V First)) 
