module Magma
import Set

%default total
%access public

infixl 6 <++>
class Set c => Magma c where
  (<++>) : c -> c -> c
  total
  plusPreservesEq : {c1,c2,c1',c2':c} -> c1 ~= c1' -> c2 ~= c2' -> c1 <++> c2 ~= c1' <++> c2'

abstract
plusPreservesEqL : Magma c => {c1,c1',c2:c} -> c1 ~= c1' -> c1 <++> c2 ~= c1' <++> c2
plusPreservesEqL {c} {c2} c1c1' = plusPreservesEq {c} c1c1' (rfl {c} {x=c2})

abstract
plusPreservesEqR : Magma c => {c1,c2,c2':c} -> c2 ~= c2' -> c1 <++> c2 ~= c1 <++> c2'
plusPreservesEqR {c} {c1} c2c2' = plusPreservesEq {c} (rfl {c} {x=c1}) c2c2'

-- The free magma over a type.
data FreeMagma : Type -> Type where
  MagSingle : (x : s) -> FreeMagma s
  MagPlus : (x,y : FreeMagma s) -> FreeMagma s

instance Set c => Set (FreeMagma c) where
  (~=) (MagSingle x) (MagSingle y) = x ~= y
  (~=) (MagSingle x) (MagPlus y z) = Void
  (~=) (MagPlus x z) (MagSingle y) = Void
  (~=) (MagPlus x z) (MagPlus y w) = (x ~= y, z ~= w)
  rfl {x = (MagSingle x)} = rfl {c}
  rfl {x = (MagPlus x y)} = (rfl {c = FreeMagma c}, rfl {c = FreeMagma c})
  symm {x = (MagSingle x)} {y = (MagSingle y)} xy = symm {c} xy
  symm {x = (MagSingle x)} {y = (MagPlus y z)} xy = absurd xy
  symm {x = (MagPlus x z)} {y = (MagSingle y)} xy = absurd xy
  symm {x = (MagPlus ps qs)} {y = (MagPlus rs ss)} (psrs, qsss) = (symm {c=FreeMagma c} psrs, symm {c=FreeMagma c} qsss)
  trns {x = (MagSingle x)} {y = (MagSingle y)} {z = (MagSingle z)} xy yz = trns {c} xy yz
  trns {x = (MagSingle x)} {y = (MagSingle y)} {z = (MagPlus z w)} xy yz = absurd yz
  trns {x = (MagSingle x)} {y = (MagPlus y w)} {z = z} xy yz = absurd xy
  trns {x = (MagPlus x w)} {y = (MagSingle y)} {z = z} xy yz = absurd xy
  trns {x = (MagPlus x1 x2)} {y = (MagPlus y1 y2)} {z = (MagSingle z)} xy yz = absurd yz
  trns {x = (MagPlus x1 x2)} {y = (MagPlus y1 y2)} {z = (MagPlus z1 z2)} (x1y1, x2y2) (y1z1, y2z2) =
    (trns {c=FreeMagma c} x1y1 y1z1, trns {c=FreeMagma c} x2y2 y2z2)

instance Set c => Magma (FreeMagma c) where
  (<++>) xs ys = MagPlus xs ys
  plusPreservesEq c1c1' c2c2' = (c1c1', c2c2')

RespectsMagma : (Magma m, Magma n) => (m -> n) -> Type
RespectsMagma {m} f = (x, y : m) -> f (x <++> y) ~= f x <++> f y

respectCompositional : (Magma m, Magma n, Magma o) =>
                       {f : n -> o} -> {g : m -> n} ->
                       IsFunction f -> RespectsMagma f ->
                       IsFunction g -> RespectsMagma g ->
                       RespectsMagma (f . g)
respectCompositional {o} {g} funF rf funG rg x y =
  let foo = rg x y
      bar = funF (g (x <++> y)) (g x <++> g y) foo
      baz = rf (g x) (g y)
  in trns {c=o} bar baz

{-
The functions fmSplit, fmSplitSplits, fmSplitRespectsMagma, fmSplitIsFunction,
and fmSplitUnique together prove that for any Set c, FreeMagma c is the free magma
over c.
-}

||| Any function from a type `c` to a magma `n` can be split into
||| a function, `MagSingle`, from `c` to `FreeMagma c` followed by a unique
||| magma morphism from `FreeMagma c` to `n`. `fmSplit` produces the function
||| from `FreeMagma c` to `n`.
fmSplit : Magma n => (f : c -> n) -> (FreeMagma c -> n)
fmSplit f (MagSingle x) = f x
fmSplit f (MagPlus x y) = fmSplit f x <++> fmSplit f y

||| fmSplit actually splits its argument.
abstract
fmSplitSplits : Magma n => (f : c -> n) -> f ~~= fmSplit f . MagSingle
fmSplitSplits {n} f x = rfl {c=n}

||| The result of `fmSplit` respects the magmas. Together with `fmSplitIsFunction`,
||| this proves the result of `fmSplit` is a magma morphism.
abstract
fmSplitRespectsMagma : (Set c, Magma n) => (f : c -> n) -> RespectsMagma {m = FreeMagma c} (fmSplit f)
fmSplitRespectsMagma {n} f (MagSingle x) (MagSingle y) = rfl {c=n}
fmSplitRespectsMagma {n} f (MagSingle x) (MagPlus y1 y2) = rfl {c=n}
fmSplitRespectsMagma {n} f (MagPlus x1 x2) (MagSingle y) = rfl {c=n}
fmSplitRespectsMagma {n} f (MagPlus x1 x2) (MagPlus y1 y2) = rfl {c=n}

||| The result of `fmSplit` is a function. Together with `fmSplitRespectsMagma`, this
||| shows that the result of `fmSplit` is a magma morphism.
abstract
fmSplitIsFunction : (Set c, Magma n) => (f : c -> n) -> IsFunction f -> IsFunction (fmSplit f)
fmSplitIsFunction {c = c} {n = n} f fIsFun (MagSingle x) (MagSingle y) xy = fIsFun x y xy
fmSplitIsFunction {c = c} {n = n} f fIsFun (MagSingle x) (MagPlus y1 y2) xy = absurd xy
fmSplitIsFunction {c = c} {n = n} f fIsFun (MagPlus x1 x2) (MagSingle y) xy = absurd xy
fmSplitIsFunction {c = c} {n = n} f fIsFun (MagPlus x1 x2) (MagPlus y1 y2) (x1y1, x2y2)
    = let hx1EQhy1 : (fmSplit f x1 ~= fmSplit f y1) = fmSplitIsFunction f fIsFun x1 y1 x1y1
          hx2EQhy2 : (fmSplit f x2 ~= fmSplit f y2) = fmSplitIsFunction f fIsFun x2 y2 x2y2
          foo : (fmSplit f (x1 <++> x2) ~= fmSplit f x1 <++> fmSplit f x2) = fmSplitRespectsMagma {c} {n} f x1 x2
          baz : (fmSplit f x1 <++> fmSplit f x2 ~= fmSplit f y1 <++> fmSplit f y2) =
            plusPreservesEq {c=n} hx1EQhy1 hx2EQhy2
          quux : (fmSplit f y1 <++> fmSplit f y2 ~= fmSplit f (y1 <++> y2))
               = symm {c=n} $ fmSplitRespectsMagma f y1 y2
          in trns {c=n} (trns {c=n} foo baz) quux

||| Any magma morphism from `FreeMagma c` to `n` that splits `f` is equivalent to
||| `fmSplit f`. The theorem is in fact slighly stronger -- the morphism does
||| not need to have been proven a "function" first.
abstract
fmSplitUnique : (Set c, Magma n) =>
                (f : c -> n) ->
                (g : FreeMagma c -> n) ->
                RespectsMagma g ->
                f ~~= g . MagSingle -> fmSplit f ~~= g
fmSplitUnique {c} {n} f g gRespMag gSplits (MagSingle x) = gSplits x
fmSplitUnique {c} {n} f g gRespMag gSplits (MagPlus x1 x2) =
  let x1unique : (fmSplit f x1 ~= g x1) = fmSplitUnique {c} {n} f g gRespMag gSplits x1
      x2unique : (fmSplit f x2 ~= g x2) = fmSplitUnique {c} {n} f g gRespMag gSplits x2
      pp : (fmSplit f x1 <++> fmSplit f x2 ~= g x1 <++> g x2) = plusPreservesEq {c=n} x1unique x2unique
      yeah : (g x1 <++> g x2 ~= g (x1 <++> x2)) = symm {c=n} $ gRespMag x1 x2
  in trns {c=n} pp yeah

||| The free magma over a magma can be collapsed down to the underlying
||| magma. In particular, `evalMag` is the unique morphism from
||| `FreeMagma s` to `s` that retracts `MagSingle`.
evalMag : Magma s => FreeMagma s -> s
evalMag = fmSplit {n=s} id

evalMagRespectsMagma : Magma c => (x,y:FreeMagma c) -> evalMag x <++> evalMag y ~= evalMag (x <++> y)
evalMagRespectsMagma {c} x y = fmSplitRespectsMagma {c} id x y

evalMagIsFunction : Magma c => IsFunction {b=c} evalMag
evalMagIsFunction {c} = fmSplitIsFunction {c} {n=c} id idIsFunction

---------- Example -----------

instance Magma Additive where
  (<++>) = (<+>)
  plusPreservesEq c1c1' c2c2' = rewrite c1c1' in rewrite c2c2' in Refl
