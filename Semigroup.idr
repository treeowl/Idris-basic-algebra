module Semigroup
import Set
import Magma
-- import Classes.Verified

%default total
%access public

class Magma c => MySemigroup c where
  plusAssoc : (c1,c2,c3:c) -> c1 <++> (c2 <++> c3) ~= c1 <++> c2 <++> c3

||| The free semigroup over a type (i.e., a type of nonempty lists)
data FreeSem : Type -> Type where
  SSingle : (x : c) -> FreeSem c
  SPlus : (x : c) -> (xs : FreeSem c) -> FreeSem c

instance Set c => Set (FreeSem c) where
  (SSingle x) ~= (SSingle y) = x ~= y
  (SSingle y) ~= (SPlus x xs) = Void
  (SPlus x xs) ~= (SSingle y) = Void
  (SPlus x xs) ~= (SPlus y ys) = (x ~= y, xs ~= ys)
  rfl {x = (SSingle x)} = rfl {c}
  rfl {x = (SPlus x xs)} = (rfl {c}, rfl {x=xs})
  symm {x = (SSingle x)} {y = (SSingle y)} xy = symm {c} xy
  symm {x = (SSingle x)} {y = (SPlus y xs)} xy = absurd xy
  symm {x = (SPlus x xs)} {y = (SSingle y)} xy = absurd xy
  symm {x = (SPlus x xs)} {y = (SPlus y z)} (xy, xsys) = (symm {c} xy, symm {c=FreeSem c} xsys)
  trns {x = (SSingle x)} {y = (SSingle y)} {z = (SSingle z)} xy yz = trns {c} xy yz
  trns {x = (SSingle x)} {y = (SSingle y)} {z = (SPlus z xs)} xy yz = absurd yz
  trns {x = (SSingle x)} {y = (SPlus y xs)} {z = z} xy yz = absurd xy
  trns {x = (SPlus x xs)} {y = (SSingle y)} {z = z} xy yz = absurd xy
  trns {x = (SPlus x xs)} {y = (SPlus y w)} {z = (SSingle z)} xy yz = absurd yz
  trns {x = (SPlus x xs)} {y = (SPlus y w)} {z = (SPlus z s)} (xy,xsys) (yz,yszs) =
    (trns {c} xy yz, trns {c=FreeSem c} xsys yszs)

sPlus : FreeSem c -> FreeSem c -> FreeSem c
sPlus (SSingle x) xs = SPlus x xs
sPlus (SPlus x xs) ys = SPlus x (xs `sPlus` ys)

abstract
plusPreservesEqFS : Set c => {c1,c1',c2,c2' : FreeSem c} -> c1 ~= c1' -> c2 ~= c2' -> sPlus c1 c2 ~= sPlus c1' c2'
plusPreservesEqFS {c1 = (SSingle x)} {c1'=(SSingle y)} {c2 = c2} {c2'=c2p} c1c1' c2c2' = (c1c1', c2c2')
plusPreservesEqFS {c1 = (SSingle x)} {c1'=(SPlus y xs)} {c2 = c2} {c2'=c2p} c1c1' c2c2' = absurd c1c1'
plusPreservesEqFS {c1 = (SPlus x xs)} {c1'=(SSingle y)} {c2 = c2} {c2'=c2p} c1c1' c2c2' = absurd c1c1'
plusPreservesEqFS {c1 = (SPlus x xs)} {c1'=(SPlus y ys)} {c2 = c2} {c2'=c2p} (xy, xsys) c2c2p =
  let foo = plusPreservesEqFS {c1=xs} {c1'=ys} {c2} {c2'=c2p} xsys c2c2p
  in (xy, foo)

instance Set c => Magma (FreeSem c) where
  (<++>) = sPlus
  plusPreservesEq = plusPreservesEqFS {c}

private
plusAssocFS : Set c => {c1,c2,c3 : FreeSem c} ->
              c1 <++> (c2 <++> c3) ~= c1 <++> c2 <++> c3

plusAssocFS {c} {c1 = (SSingle x)} = (rfl {c}, rfl {c=FreeSem c})
plusAssocFS {c} {c1 = (SPlus x xs)} = (rfl {c}, plusAssocFS {c})

instance Set c => MySemigroup (FreeSem c) where
  plusAssoc {c1} {c2} {c3} = plusAssocFS {c} {c1} {c2} {c3}

-- The functions `fsSplit`, `fsSplitSplits`, `fsSplitRespectsSem`, `fsSplitIsFunction`,
-- and `fsSplitUnique` together prove that `FreeSem c` with injection `SSingle`
-- is the free semigroup for a set `c`.

||| Any function from a type `c` to a semigroup `n` can be split into
||| a function, `MagSingle`, from `c` to `FreeSem c` followed by a unique
||| homomorphism from `FreeSem c` to `n`. `fsSplit` produces the function
||| from `FreeSem c` to `n`.
fsSplit : Magma s => (f : c -> s) -> (FreeSem c -> s)
fsSplit f (SSingle x) = f x
fsSplit f (SPlus x xs) = f x <++> fsSplit f xs

||| fmSplit actually splits its argument.
fsSplitSplits : Magma s => (f : c -> s) -> f ~~= fsSplit f . SSingle
fsSplitSplits {s} f x = rfl {c=s}

||| The result of `fsSplit` respects the semigroups. Together with `fsSplitIsFunction`,
||| this proves the result of `fsSplit` is a homomorphism.
fsSplitRespectsSem : (Set c, MySemigroup s) => (f : c -> s) -> RespectsMagma {m = FreeSem c} (fsSplit f)
fsSplitRespectsSem {s} f (SSingle x) (SSingle y) = rfl {c=s}
fsSplitRespectsSem {s} f (SSingle x) (SPlus y1 y2) = rfl {c=s}
fsSplitRespectsSem {s} f (SPlus x1 x2) y =
  let
      foo : (fsSplit f (x2 <++> y) ~= fsSplit f x2 <++> fsSplit f y)
          = fsSplitRespectsSem {s} f x2 y

      bar : ( f x1 <++> fsSplit f (x2 <++> y) ~= f x1 <++> (fsSplit f x2 <++> fsSplit f y) )
          = plusPreservesEqR {c=s} {c1=f x1} {c2=fsSplit f (x2 <++> y)} {c2'=fsSplit f x2 <++> fsSplit f y} foo

      baz = plusAssoc (f x1) (fsSplit f x2) (fsSplit f y)
  in trns {c=s} bar baz

||| The result of `fsSplit` is a well-defined function. Together with
||| `fsSplitRespectsSem`, this proves it is a homomorphism.
fsSplitIsFunction : (Set c, Magma s) => (f : c -> s) -> IsFunction f ->
                    (x,y : FreeSem c) -> x ~= y -> fsSplit f x ~= fsSplit f y
fsSplitIsFunction f fIsFun (SSingle x) (SSingle y) xy = fIsFun x y xy
fsSplitIsFunction f fIsFun (SSingle x) (SPlus y xs) xy = absurd xy
fsSplitIsFunction f fIsFun (SPlus x xs) (SSingle y) xy = absurd xy
fsSplitIsFunction {s} f fIsFun (SPlus x xs) (SPlus y ys) (xy, xsys) =
  let foo = fIsFun x y xy
      bar = fsSplitIsFunction f fIsFun xs ys xsys
  in plusPreservesEq {c=s} foo bar

||| The morphism produced by `fsSplit` is unique.
fsSplitUnique : (Set c, MySemigroup n) =>
                (f : c -> n) ->
                (g : FreeSem c -> n) ->
                RespectsMagma g ->
                f ~~= g . SSingle -> fsSplit f ~~= g
fsSplitUnique f g gRespMag gSplitsf (SSingle x) = gSplitsf x
fsSplitUnique {n} f g gRespMag gSplitsf (SPlus x xs) =
  let
      foo : (fsSplit f xs ~= g xs)
          = fsSplitUnique f g gRespMag gSplitsf xs
      bar : (g (SSingle x) <++> g xs ~= g (SSingle x <++> xs))
          = symm {c=n} $ gRespMag (SSingle x) xs
      baz : (f x ~= g (SSingle x))
          = gSplitsf x
      quux : (f x <++> fsSplit f xs ~= g (SSingle x) <++> g xs)
          = plusPreservesEq {c=n} baz foo
  in trns {c=n} quux bar

||| The free semigroup over a semigroup can be collapsed down to the
||| underlying semigroup. `evalS` is the (unique) retraction of
||| `SSingle`.
evalS : MySemigroup c => FreeSem c -> c
evalS {c} = fsSplit {s=c} id

evalSIsFunction : MySemigroup c => IsFunction (evalS {c})
evalSIsFunction {c} x y xy = fsSplitIsFunction {c} id idIsFunction x y xy

||| We can take the free magma to the free semigroup in a unique
||| way that factors `SSingle`. That is, by the properties of `fmSplit`,
||| `canonS` is a morphism, `canonS . MagSingle ~~= SSingle`, and
||| `canonS` is the only such morphism. What does this mean, and why is
||| it useful? The equivalence above just says that if we take a
||| single value, form it into an expression with MagSingle, and pass that
||| expression to `canonS`, then we will get the same expression we would
||| get by applying `SSingle` to the value. The fact that it is a morphism
||| means that adding two expressions adds (appends) the `canonS` results.
||| Uniqueness means there's only one way to do it; the result of `canonS`
||| is completely determined by algebraic properties, and not by any details
||| of its implementation.
canonS : Set c => FreeMagma c -> FreeSem c
canonS = fmSplit SSingle

SSingleIsFunction : Set s => (x, y : s) -> x ~= y -> SSingle x ~= SSingle y
SSingleIsFunction x y xy = xy

canonSWorks_lem1 : MySemigroup s => id ~~= fsSplit {s} id . fmSplit {n=FreeSem s} SSingle . MagSingle
canonSWorks_lem1 {s} x = rfl {c=s}  -- This must be proof by computation. Spooky.

||| Applying `canonS` to an expression (represented by a free magma) is guaranteed
||| to produce an expression (represented by a free semigroup) that evaluates to
||| the same thing.
abstract
canonSWorks : MySemigroup s => (fm : FreeMagma s) -> evalMag fm ~= evalS (canonS fm)
canonSWorks {s} fm =
  -- The length of this function makes me sad. Maybe there is some way to clean it up.
  let
     -- Why do we need this horrible thing?
     huh : (Set s) = %instance
     resp : (RespectsMagma (fsSplit id . fmSplit {c=s} SSingle))
          = respectCompositional {f=fsSplit id} {g=fmSplit {c=s} SSingle}
              (fsSplitIsFunction {c=s} id (\x,y,xy=>xy))
              (fsSplitRespectsSem id)
              (fmSplitIsFunction SSingle SSingleIsFunction)  -- g is well-defined
              (fmSplitRespectsMagma SSingle)
     foo  : (fmSplit id ~~= fsSplit id . fmSplit SSingle)
          = fmSplitUnique {c=s} {n=s} id (fsSplit id . fmSplit SSingle) resp canonSWorks_lem1
  in foo fm

solveSemigroup : MySemigroup a => (xs, ys : FreeMagma a) -> {default Refl canonSame : canonS xs = canonS ys} ->
                            evalMag xs ~= evalMag ys
solveSemigroup {a} {canonSame} xs ys =
  let fooxs = canonSWorks {s=a} xs
      fooys = symm {c=a} $ canonSWorks {s=a} ys
  in ?solveSemigroup_rhs

testing : MySemigroup s => (x,y,z,w,p:s) ->
          x <++> (y <++> (z <++> p) <++> w) ~= x <++> y <++> (z <++> (p <++> w))
testing {s} x y z w p = 
  -- Why do I need this???
  let huh : (Set s) = %instance
  in solveSemigroup
          (MagSingle x <++> ((MagSingle y <++> (MagSingle z <++> MagSingle p)) <++> MagSingle w))
          ((MagSingle x <++> MagSingle y) <++> (MagSingle z <++> (MagSingle p <++> MagSingle w)))

testing2 : MySemigroup s => (x,y,z,w,p:s) ->
          x <++> (y <++> (z <++> p) <++> w) ~= x <++> y <++> (z <++> (p <++> w))
testing2 x y z w p = solveSemigroup
          (MagSingle x `MagPlus` ((MagSingle y `MagPlus` (MagSingle z `MagPlus` MagSingle p)) `MagPlus` MagSingle w))
          ((MagSingle x `MagPlus` MagSingle y) `MagPlus` (MagSingle z `MagPlus` (MagSingle p `MagPlus` MagSingle w)))

-- Sometimes plain old equality is good enough, and we don't need general
-- equivalences. For these situations, we want to offer a plain version.

{-
data Wrap a = MkWrap a
unwrap : Wrap a -> a
unwrap (MkWrap x) = x

instance VerifiedSemigroup s => Set (Wrap s) where
  (~=) = (~=~)
  rfl = Refl
  symm = sym
  trns = trans

instance VerifiedSemigroup s => Magma (Wrap s) where
  (<++>) (MkWrap x) (MkWrap y) = MkWrap (x <+> y)
  plusPreservesEqL c1c1' = rewrite sym c1c1' in Refl
  plusPreservesEqR c2c2' = cong c2c2'

instance VerifiedSemigroup s => MySemigroup (Wrap s) where
  plusAssoc (MkWrap x1) (MkWrap x2) (MkWrap x3) =
    cong $ semigroupOpIsAssociative x1 x2 x3

testing : MySemigroup s => (x,y,z,w,p:s) ->
          x <++> (y <++> (z <++> p) <++> w) ~= x <++> y <++> z <++> p <++> w
testing x y z w p = scWorks $
          SSingle x `SPlus` ((SSingle y `SPlus` (SSingle z `SPlus` SSingle p)) `SPlus` SSingle w)

instance VerifiedSemigroup Additive where
  semigroupOpIsAssociative (getAdditive x) (getAdditive y) (getAdditive z)
    = cong $ plusAssociative x y z

testingWrap : VerifiedSemigroup s => (x,y,z,w,p:s) ->
          x <+> (y <+> (z <+> p) <+> w) = x <+> y <+> z <+> p <+> w
testingWrap x y z w p =
   let foo = scWorks $
          SSingle (MkWrap x) `SPlus` ((SSingle (MkWrap y) `SPlus` (SSingle (MkWrap z) `SPlus` SSingle (MkWrap p))) `SPlus` SSingle (MkWrap w))
   in cong {f=unwrap} foo
   -}


---------- Proofs ----------

solveSemigroup_rhs = proof
  intro a,xs,ys
  intro
  intro
  rewrite canonSame 
  intros
  exact trns {c=a} fooxs fooys

