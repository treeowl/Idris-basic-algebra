module Set

%default total
%access public

infixl 4 ~=
class Set c where
  (~=) : (x,y:c) -> Type

  rfl : {x:c} -> x ~= x
  symm : {x,y:c} -> x ~= y -> y ~= x
  trns : {x,y,z:c} -> x ~= y -> y ~= z -> x ~= z

infix 5 ~~=
||| Equivalence of functions
(~~=) : Set b => (a -> b) -> (a -> b) -> Type
(~~=) {a} f g = (x : a) -> f x ~= g x

IsFunction : (Set a, Set b) => (a -> b) -> Type
IsFunction {a} {b} f = (x, y : a) -> x ~= y -> f x ~= f y

idIsFunction : Set a => (x,y:a) -> (x ~= y) -> id x ~= id y
idIsFunction x y xy = xy

functionsCompose : (Set a, Set b, Set c) =>
                   {f : b -> c} ->
                   {g : a -> b} ->
                   IsFunction f ->
                   IsFunction g ->
                   IsFunction (f . g)
functionsCompose {g} fIsFun gIsFun x y xy = fIsFun (g x) (g y) (gIsFun x y xy)

abstract
eqPreservesEq : Set c -> (x,y,c1,c2:c) -> x ~= c1 -> y ~= c2 -> c1 ~= c2 -> x ~= y
eqPreservesEq {c} setc x y c1 c2 xc1 yc2 c1c2 =
  let xc2 : (x ~= c2) = trns {c} xc1 c1c2
      c2y : (c2 ~= y) = symm {c} yc2
  in trns {c} xc2 c2y

class Functor f => MyFunctor (f : Type -> Type) where
  myFunctorIdentity : Set (f c) => map id ~~= id
  myFunctorComposition : Set (f c) => (g1 : a -> b) -> (g2 : b -> c) -> map (g2 . g1) ~~= (map g2 . map g1)


----------------  Demos   ----------------

instance Set t => Set (Maybe t) where
  (~=) Nothing Nothing = ()
  (~=) Nothing (Just x) = Void
  (~=) (Just x) Nothing = Void
  (~=) (Just x) (Just y) = (x~=y)
  rfl {x = Nothing} = ()
  rfl {x = (Just x)} = rfl {c=t}
  symm {x = Nothing} {y = Nothing} xy = ()
  symm {x = Nothing} {y = (Just x)} xy = absurd xy
  symm {x = (Just x)} {y = Nothing} xy = absurd xy
  symm {x = (Just x)} {y = (Just y)} xy = symm {c=t} xy
  trns {x = Nothing} {y = Nothing} {z = Nothing} xy yz = ()
  trns {x = Nothing} {y = Nothing} {z = (Just x)} xy yz = absurd yz
  trns {x = Nothing} {y = (Just x)} {z = z} xy yz = absurd xy
  trns {x = (Just x)} {y = Nothing} {z = z} xy yz = absurd xy
  trns {x = (Just x)} {y = (Just y)} {z = Nothing} xy yz = absurd yz
  trns {x = (Just x)} {y = (Just y)} {z = (Just z)} xy yz = trns {c=t} xy yz

instance Set Nat where
  (~=) = (~=~)
  rfl = Refl
  symm = sym
  trns = trans

instance Set Additive where
  (~=) = (~=~)
  rfl = Refl
  symm = sym
  trns = trans
