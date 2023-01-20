module Multiplate

import Control.Monad.Identity
import Control.Applicative.Const

%default total

||| A projector represents a field of a plate
public export 0
Projector : ((Type -> Type) -> Type) -> Type -> Type
Projector p a = forall f. p f -> a -> f a

||| A plate is represents a set of applicative transforms over a type
||| where each transform can be applied to sub-nodes of the type.
|||
||| Additionally new plates can be built from a function
||| which is generic over the type of nodes.
|||
||| @ p a plate parametised by an applicative functor
public export
interface Multiplate (0 p : (Type -> Type) -> Type) where
    ||| Take a plate and return a new plate,
    ||| which applies each transform in the old plate
    ||| to the direct children of each node.
    total
    multiplate : Applicative f => p f -> p f
    ||| Create a plate using a generic projector function
    total
    mkPlate : Applicative f => (forall a. Projector p a -> a -> f a) -> p f

||| A plate which 'does nothing' ie applies `pure` to each node.
public export total
purePlate : Multiplate p => Applicative f => p f
purePlate = mkPlate (\_ => pure)

||| Apply a natural transform to a plate
public export
applyNaturalTransform : Multiplate p => Applicative g => (forall a. f a -> g a) -> p f -> p g
applyNaturalTransform f p = mkPlate $ \proj, x => f $ proj p x

public export
fromIdentity : Multiplate p => Applicative f => p Identity -> p f
fromIdentity = applyNaturalTransform (pure . runIdentity)

infixl 5 `andThenM`

||| Compose 2 plates, by applying them from left to right.
public export
andThenM : Monad m => Multiplate p => Lazy (p m) -> Lazy (p m) -> p m
andThenM p1 p2 = mkPlate $ \proj, x => do
    x' <- proj p1 x
    proj p2 x'

infixl 5 `andThenId`

||| Compose 2 plates, where the second is based on the identity functor
public export
andThenId : Multiplate p => Applicative m => Lazy (p m) -> Lazy (p Identity) -> p m
andThenId p1 p2 = mkPlate $ \proj, x => proj p1 x <&> \x' => runIdentity (proj p2 x')

infixl 5 `iAndThen`

||| Compose 2 plates, where the first is based on the identity functor
public export
idAndThen : Multiplate p => Applicative m => Lazy (p Identity) -> Lazy (p m) -> p m
idAndThen p1 p2 = mkPlate $ \proj, x =>
    let x' = runIdentity $ proj p1 x
     in proj p2 x'

infixr 4 `orElse`

||| Compose 2 plates, by trying the first and then the second
public export
orElse : Alternative m => Multiplate p => Lazy (p m) -> Lazy (p m) -> p m
orElse p1 p2 = mkPlate $ \proj, x => proj p1 x <|> proj p2 x

||| Apply a transformation to the whole family of a node.
||| This happens in a depth-first order
public export covering
mapFamily : Multiplate p => Monad m => p m -> p m
mapFamily p = multiplate (mapFamily p) `andThenM` p

||| Append the result of 2 plates which each return `Const`
public export
append : Multiplate p => Monoid o => Lazy (p (Const o)) -> Lazy (p (Const o)) -> p (Const o)
append p1 p2 = mkPlate $ \proj, x => proj p1 x <+> proj p2 x

||| Apply a fold to the whole family of a node.
|||
||| The result, when applied to `x` looks like:
||| ```
||| x
|||     <+> children x
|||     <+> grandchildren x
|||     ...
||| ```
public export covering
preorderFold : Multiplate p => Monoid o => p (Const o) -> p (Const o)
preorderFold p = p `append` multiplate (preorderFold p)

public export covering
postorderFold : Multiplate p => Monoid o => p (Const o) -> p (Const o)
postorderFold p = multiplate (postorderFold p) `append` p 

||| Remove a `Maybe` from a transformation by providing a plate which generates a default value.
public export
catchWith : Multiplate p => Applicative f => p Maybe -> p f -> p f
catchWith p def = mkPlate $ \proj, x => case proj p x of
    Just x' => pure x'
    Nothing => proj def x

||| Remove a `Maybe` from a transformation by returning the original value unaltered.
|||
||| This is equivalent to `catchWith purePlate`
public export
catch : Multiplate p => Applicative f => p Maybe -> p f
catch p = mkPlate $ \proj, x => case proj p x of
    Just x' => pure x'
    Nothing => pure x

||| Plates tend to have one field per mutually recursive data type.
||| This interface allows for projecting the transform of @ a
||| or making a new plate, which applies a transform to @ a.
|||
||| @ p the plate
||| @ a the field
public export
interface Multiplate p => HasField p a where
    ||| Project a transform of a specific field out of a plate.
    total
    project : Projector p a
    ||| Inject a transform to create a new plate.
    total
    inject : Applicative f => (a -> f a) -> p f
    inject f = update f purePlate
    ||| Update the transform of a given field.
    total
    update : (a -> f a) -> p f -> p f

||| Run a transformation in the identity monad.
|||
||| To run transforms in a different Monad use `project`
public export
traverseFor : HasField p a => p Identity -> a -> a
traverseFor p x = runIdentity $ project p x

||| Run a fold
public export
foldFor : HasField p a => p (Const o) -> a -> o
foldFor p x = runConst $ project p x
