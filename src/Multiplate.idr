||| Multiplate allows for traversals over mutually recursive data types,
||| while removing a lot of the boilerplate.
|||
||| After writting some initial boilerplate, you can write much shorter
||| and clearer transformations, as you don't need to manually recurse on each subterm.
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
||| This works fine with indexed data types -
||| see `tests/Multiplate/Tests/DeBruijn.idr` for an expression using De Bruijn indexes.
||| You may need to beta-expand in the definition of `mkPlate` (ie change `build expr` to `build (\p => expr p)`)
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
public export %inline
purePlate : Multiplate p => Applicative f => p f
purePlate = mkPlate (\_ => pure)

||| Apply a natural transform to a plate
public export %inline
applyNaturalTransform : Multiplate p => Applicative g => (forall a. f a -> g a) -> p f -> p g
applyNaturalTransform f p = mkPlate $ \proj, x => f $ proj p x

public export %inline
fromIdentity : Multiplate p => Applicative f => p Identity -> p f
fromIdentity = applyNaturalTransform (pure . runIdentity)

infixl 5 `andThenM`

||| Compose 2 plates, by applying them from left to right.
public export %inline
andThenM : Monad m => Multiplate p => Lazy (p m) -> Lazy (p m) -> p m
andThenM p1 p2 = mkPlate $ \proj, x => do
    x' <- proj p1 x
    proj p2 x'

infixl 5 `andThenId`

||| Compose 2 plates, where the second is based on the identity functor
public export %inline
andThenId : Multiplate p => Applicative m => Lazy (p m) -> Lazy (p Identity) -> p m
andThenId p1 p2 = mkPlate $ \proj, x => proj p1 x <&> \x' => runIdentity (proj p2 x')

infixl 5 `iAndThen`

||| Compose 2 plates, where the first is based on the identity functor
public export %inline
idAndThen : Multiplate p => Applicative m => Lazy (p Identity) -> Lazy (p m) -> p m
idAndThen p1 p2 = mkPlate $ \proj, x =>
    let x' = runIdentity $ proj p1 x
     in proj p2 x'

infixr 4 `orElse`

||| Compose 2 plates, by trying the first and then the second
public export %inline
orElse : Alternative m => Multiplate p => Lazy (p m) -> Lazy (p m) -> p m
orElse p1 p2 = mkPlate $ \proj, x => proj p1 x <|> proj p2 x

||| Apply a transformation to the whole family of a node.
||| This happens in a post-order, ie children are mapped before parents.
public export covering
postorderMap : Multiplate p => Monad m => p m -> p m
postorderMap p = multiplate (postorderMap p) `andThenM` p

||| Apply a transformation to the whole family of a node.
||| This happens in a pre-order, ie parents are mapped before children.
public export covering
preorderMap : Multiplate p => Monad m => p m -> p m
preorderMap p = p `andThenM` multiplate (preorderMap p)

||| Append the result of 2 plates which each return `Const`
public export %inline
append : Multiplate p => Monoid o => Lazy (p (Const o)) -> Lazy (p (Const o)) -> p (Const o)
append p1 p2 = mkPlate $ \proj, x => proj p1 x <+> proj p2 x

||| Apply a fold to the whole family of a node.
||| This applies to the parent node, followed by children.
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

||| Apply a fold to the whole family of a node.
||| This applies to the children, followed by the parent node.
|||
||| The result when applied to `x` looks like:
||| ```
||| ...
|||     <+> grandchildren x
|||     <+> children x
|||     <+> x
public export covering
postorderFold : Multiplate p => Monoid o => p (Const o) -> p (Const o)
postorderFold p = multiplate (postorderFold p) `append` p 

||| Remove a `Maybe` from a transformation by providing a plate which generates a default value.
public export %inline
catchWith : Multiplate p => Applicative f => p Maybe -> p f -> p f
catchWith p def = mkPlate $ \proj, x => case proj p x of
    Just x' => pure x'
    Nothing => proj def x

||| Remove a `Maybe` from a transformation by returning the original value unaltered.
|||
||| This is equivalent to `catchWith purePlate`
public export %inline
catch : Multiplate p => Applicative f => p Maybe -> p f
catch p = mkPlate $ \proj, x => case proj p x of
    Just x' => pure x'
    Nothing => pure x

||| Plates tend to consist of a fixed set of fields.
||| This interface allows for projecting the transform of @ a.
|||
||| @ p the plate
||| @ a the field
public export
interface Multiplate p => HasProjection p a where
    ||| Project a transform of a specific field out of a plate.
    total
    project : Projector p a

||| Run a transformation in the identity monad.
|||
||| To run transforms in a different Monad use `project`
public export %inline
traverseFor : HasProjection p a => p Identity -> a -> a
traverseFor p x = runIdentity $ project p x

||| Run a fold
public export %inline
foldFor : HasProjection p a => p (Const o) -> a -> o
foldFor p x = runConst $ project p x

||| Plates tend to consist of a fixed set of fields.
||| In addition to being able to project a field,
||| this interface allows for creating a plate from a transform.
|||
||| This is seperate from `HasProjection` as it is typically not
||| possible to implement for plates with indexed data types.
|||
||| @ p the plate
||| @ a the field
public export
interface HasProjection p a => HasField p a where
    ||| Inject a transform to create a new plate,
    ||| by filling in other transforms with `pure`.
    total
    inject : Applicative f => (a -> f a) -> p f
    inject f = update f purePlate
    ||| Update the transform of a given field,
    ||| by replacing it with a new transform.
    total
    update : (a -> f a) -> p f -> p f

||| Inject a pure transformation into a plate.
public export %inline
injectPure : HasField p a => Applicative f => (a -> a) -> p f
injectPure f = inject $ pure . f
