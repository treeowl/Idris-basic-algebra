module Monoid
import Set
import Magma
import Semigroup

%default total
%access public

class MySemigroup c => MyMonoid c where
  Neutral : c
  neutralLeftNeutral : (c1 : c) -> Neutral <++> c1 ~= c1
  neutralRightNeutral : (c1 : c) -> c1 <++> Neutral ~= c1

||| Anything equivalent to the designated neutral element is left neutral.
abstract
neutralsLeftNeutral : MyMonoid c => (z, x : c) -> (z ~= Neutral) -> z <++> x ~= x
neutralsLeftNeutral {c} z x zNeutral =
  let foo : (Neutral <++> x ~= x) = neutralLeftNeutral x
      bar = plusPreservesEqL {c} {c2=x} zNeutral
  in trns {c} bar foo

||| Anything equivalent to the designated neutral element is right neutral.
abstract
neutralsRightNeutral : MyMonoid c => (z, x : c) -> (z ~= Neutral) -> x <++> z ~= x
neutralsRightNeutral {c} z x zNeutral =
  let foo : (x <++> Neutral ~= x) = neutralRightNeutral x
      bar = plusPreservesEqR {c} {c1=x} zNeutral
  in trns {c} bar foo

||| Anything that behaves like a left neutral is actually equivalent
||| to `Neutral`.
neutralsEquivNeutral : MyMonoid c =>
                       (x : c) ->
                       ((y : c) -> x <++> y ~= y) ->
                       x ~= Neutral
neutralsEquivNeutral {c} x f with (f Neutral)
  neutralsEquivNeutral {c} x f | xNisN =
    let xisXN = symm {c} $ neutralRightNeutral x
    in trns {c} {x} {y=x<++>Neutral} {z=Neutral} xisXN xNisN


instance Set c => Set (List c) where
  (~=) [] [] = ()
  (~=) [] (x :: xs) = Void
  (~=) (x :: xs) [] = Void
  (~=) (x :: xs) (y :: ys) = (x ~= y, xs ~= ys)
  rfl {x = []} = ()
  rfl {x = (x :: xs)} = (rfl {c}, rfl {c=List c})
  symm {x = []} {y = []} xy = ()
  symm {x = []} {y = (x :: xs)} xy = absurd xy
  symm {x = (x :: xs)} {y = []} xy = absurd xy
  symm {x = (x :: xs)} {y = (y :: ys)} (xy, xsys) = (symm {c} xy, symm {c=List c} xsys)
  trns {x = []} {y = []} {z = []} xy yz = ()
  trns {x = []} {y = []} {z = (x :: xs)} xy yz = absurd yz
  trns {x = []} {y = (x :: xs)} {z = z} xy yz = absurd xy
  trns {x = (x :: xs)} {y = []} {z = z} xy yz = absurd xy
  trns {x = (x :: xs)} {y = (y :: ys)} {z = []} xy yz = absurd yz
  trns {x = (x :: xs)} {y = (y :: ys)} {z = (z :: zs)} (xy, xsys) (yz,yszs) = (trns {c} xy yz, trns {c=List c} xsys yszs)

headsEq : Set c => (x,y : c) -> (xs,ys : List c) -> x :: xs ~= y :: ys -> x ~= y
headsEq x y xs ys (a, b) = a

tailsEq : Set c => (x,y : c) -> (xs,ys : List c) -> x :: xs ~= y :: ys -> xs ~= ys
tailsEq x y xs ys (a, b) = b

plusPreservesEqList : Set c => {c1,c1',c2,c2' : List c} -> c1 ~= c1' -> c2 ~= c2' -> c1 ++ c2 ~= c1' ++ c2'
plusPreservesEqList {c1=[]} {c1'=[]} {c2} {c2'} c1c1' c2c2' = c2c2'
plusPreservesEqList {c1=[]} {c1'=x::xs} {c2} {c2'} c1c1' c2c2' = absurd c1c1'
plusPreservesEqList {c1=x::xs} {c1'=[]} {c2} {c2'} c1c1' c2c2' = absurd c1c1'
plusPreservesEqList {c1=x::xs} {c1'=y::ys} {c2} {c2'} c1c1' c2c2' =
  let foo = tailsEq x y xs ys c1c1'
  in (headsEq x y xs ys c1c1', plusPreservesEqList {c1=xs} {c1'=ys} foo c2c2')

instance Set c => Magma (List c) where
  (<++>) = (++)
  plusPreservesEq = plusPreservesEqList {c}

instance Set c => MySemigroup (List c) where
  plusAssoc c1 c2 c3 = rewrite appendAssociative c1 c2 c3 in rfl {c=List c}

instance Set c => MyMonoid (List c) where
  Neutral = []
  neutralLeftNeutral x = rfl {c=List c}
  neutralRightNeutral x = rewrite appendNilRightNeutral x in rfl {c=List c}

single : c -> List c
single = (::[])

-- `fMonSplit`, `fMonSplitSplits`, `fMonSplitRespectsMon`, `fMonSplitPreservesNeutral`, `fMonSplitIsFunction`,
-- and `fMonSplitUnique` together show that `List c` is the free monoid over `c`.

fMonSplit : MyMonoid m => (c -> m) -> (List c -> m)
fMonSplit f [] = Neutral
fMonSplit f (x :: xs) = f x <++> fMonSplit f xs

fMonSplitSplits : MyMonoid m => (f : c -> m) -> f ~~= fMonSplit f . single
fMonSplitSplits {m} f x = symm {c=m} $ neutralRightNeutral {c=m} (f x)

fMonSplitRespectsMon : (Set c, MyMonoid m) => (f : c -> m) -> RespectsMagma {m = List c} (fMonSplit f)
fMonSplitRespectsMon {m} f [] ys = symm {c=m} $ neutralLeftNeutral {c=m} (fMonSplit f ys)
fMonSplitRespectsMon {m} f (x::xs) ys with (fMonSplitRespectsMon f xs ys)
  fMonSplitRespectsMon {m} f (x::xs) ys | with_pat =
    let foo = plusPreservesEqR {c=m} {c1=f x} with_pat
        bar = plusAssoc (f x) (fMonSplit f xs) (fMonSplit f ys)
    in trns {c=m} foo bar

fMonSplitPreservesNeutral : (Set c, MyMonoid m) => (f : c -> m) -> fMonSplit f [] ~= Neutral
fMonSplitPreservesNeutral {m} f = rfl {c=m}

fMonSplitIsFunction : (Set c, MyMonoid m) => (f : c -> m) -> IsFunction f -> IsFunction (fMonSplit f)
fMonSplitIsFunction {m} f fIsFun [] [] xsys = rfl {c=m}
fMonSplitIsFunction f fIsFun [] (y :: ys) xsys = absurd xsys
fMonSplitIsFunction f fIsFun (x::xs) [] xsys = absurd xsys
fMonSplitIsFunction f fIsFun (x::xs) (y::ys) (xy, xsys) with (fIsFun x y xy, fMonSplitIsFunction f fIsFun xs ys xsys)
  fMonSplitIsFunction f fIsFun (x::xs) (y::ys) (xy, xsys) | (this,rec) =
    plusPreservesEq {c1=f x} {c2=fMonSplit f xs} {c1'=f y} {c2'=fMonSplit f ys} this rec

fMonSplitUnique : (Set c, MyMonoid n) =>
                  (f : c -> n) ->
                  (g : List c -> n) ->
                  RespectsMagma g ->
                  (g Neutral ~= Neutral) ->
                  f ~~= g . single -> fMonSplit f ~~= g

fMonSplitUnique {n} f g gRespMag gPresNeutral fgsingle [] = symm {c=n} gPresNeutral
fMonSplitUnique {c} {n} f g gRespMag gPresNeutral fgsingle (x::xs) with
               (fMonSplitUnique {c} {n} f g gRespMag gPresNeutral fgsingle xs)
  fMonSplitUnique {n} f g gRespMag gPresNeutral fgsingle (x::xs) | rec =
    let
        foo = fgsingle x
        bar = plusPreservesEq {c=n} foo rec
        baz = symm {c=n} $ gRespMag [x] xs
    in trns {c=n} {y=g [x] <++> g xs} {z=g ([x] ++ xs)} bar baz


||| A convenient representation of a monoid expression. This is translated
||| very simply to a nicer form for analysis.
%elim
data MonoidExpr : Type -> Type where
  NeutralE : MonoidExpr a
  MonSingle : a -> MonoidExpr a
  MonPlus : MonoidExpr a -> MonoidExpr a -> MonoidExpr a

||| A term in a "monoid expression" is either neutral or an element of the
||| underlying set. This is a copy of `Maybe` with a Haskell-like
||| `MySemigroup` instance.
%elim
data MonoidTerm : Type -> Type where
  MTNeutral : MonoidTerm a
  MTSingle : a -> MonoidTerm a

instance Functor MonoidTerm where
  map f MTNeutral = MTNeutral
  map f (MTSingle x) = MTSingle (f x)

instance MyFunctor MonoidTerm where
  myFunctorIdentity {c} MTNeutral = rfl {c=MonoidTerm c}
  myFunctorIdentity {c} (MTSingle x) = rfl {c=MonoidTerm c}
  myFunctorComposition {c} f g MTNeutral = rfl {c=MonoidTerm c}
  myFunctorComposition {c} f g (MTSingle x) = rfl {c=MonoidTerm c}

instance Set c => Set (MonoidTerm c) where
  (~=) MTNeutral MTNeutral = ()
  (~=) MTNeutral (MTSingle x) = Void
  (~=) (MTSingle x) MTNeutral = Void
  (~=) (MTSingle x) (MTSingle y) = x ~= y
  rfl {x = MTNeutral} = ()
  rfl {x = (MTSingle x)} = rfl {c}
  symm {x = MTNeutral} {y = MTNeutral} xy = ()
  symm {x = MTNeutral} {y = (MTSingle x)} xy = absurd xy
  symm {x = (MTSingle x)} {y = MTNeutral} xy = absurd xy
  symm {x = (MTSingle x)} {y = (MTSingle y)} xy = symm {c} xy
  trns {x = MTNeutral} {y = MTNeutral} {z = MTNeutral} xy yz = ()
  trns {x = MTNeutral} {y = MTNeutral} {z = (MTSingle x)} xy yz = absurd yz
  trns {x = MTNeutral} {y = (MTSingle x)} {z = z} xy yz = absurd xy
  trns {x = (MTSingle x)} {y = MTNeutral} {z = z} xy yz = absurd xy
  trns {x = (MTSingle x)} {y = (MTSingle y)} {z = MTNeutral} xy yz = absurd yz
  trns {x = (MTSingle x)} {y = (MTSingle y)} {z = (MTSingle z)} xy yz = trns {c} xy yz

instance Magma c => Magma (MonoidTerm c) where
  MTNeutral <++> MTNeutral = MTNeutral
  (MTSingle x) <++> MTNeutral = MTSingle x
  MTNeutral <++> (MTSingle y) = MTSingle y
  (MTSingle x) <++> (MTSingle y) = MTSingle (x <++> y)

  plusPreservesEq {c1 = MTNeutral} {c2 = MTNeutral} {c1' = MTNeutral} {c2' = MTNeutral} c1c1p c2c2' = ()
  plusPreservesEq {c1 = MTNeutral} {c2 = MTNeutral} {c1' = MTNeutral} {c2' = (MTSingle x)} c1c1p c2c2' = absurd c2c2'
  plusPreservesEq {c1 = MTNeutral} {c2 = MTNeutral} {c1' = (MTSingle x)} c1c1' c2c2' = absurd c1c1'
  plusPreservesEq {c1 = MTNeutral} {c2 = (MTSingle x)} {c1' = MTNeutral} {c2' = MTNeutral} c1c1' c2c2' = absurd c2c2'
  plusPreservesEq {c1 = MTNeutral} {c2 = (MTSingle x)} {c1' = MTNeutral} {c2' = (MTSingle y)} c1c1' c2c2' = c2c2'
  plusPreservesEq {c1 = MTNeutral} {c2 = (MTSingle x)} {c1' = (MTSingle y)} {c2' = c2p} c1c1' c2c2' = absurd c1c1'
  plusPreservesEq {c1 = (MTSingle x)} {c2 = c2} {c1' = MTNeutral} {c2' = c2p} c1c1' c2c2' = absurd c1c1'
  plusPreservesEq {c1 = (MTSingle x)} {c2 = MTNeutral} {c1' = (MTSingle y)} {c2' = MTNeutral} c1c1' c2c2' = c1c1'
  plusPreservesEq {c1 = (MTSingle x)} {c2 = MTNeutral} {c1' = (MTSingle y)} {c2' = (MTSingle z)} c1c1' c2c2' = absurd c2c2'
  plusPreservesEq {c1 = (MTSingle x)} {c2 = (MTSingle z)} {c1' = (MTSingle y)} {c2' = MTNeutral} c1c1' c2c2' = absurd c2c2'
  plusPreservesEq {c1 = (MTSingle x)} {c2 = (MTSingle z)} {c1' = (MTSingle y)} {c2' = (MTSingle w)} c1c1' c2c2' =
    plusPreservesEq {c1 = x} {c2 = z} {c1' = y} {c2' = w} c1c1' c2c2'

instance MySemigroup c => MySemigroup (MonoidTerm c) where
  plusAssoc MTNeutral MTNeutral MTNeutral = ()
  plusAssoc MTNeutral MTNeutral (MTSingle x) = rfl {c}
  plusAssoc MTNeutral (MTSingle x) MTNeutral = rfl {c}
  plusAssoc MTNeutral (MTSingle x) (MTSingle y) = rfl {c}
  plusAssoc (MTSingle x) MTNeutral MTNeutral = rfl {c}
  plusAssoc (MTSingle x) MTNeutral (MTSingle y) = rfl {c}
  plusAssoc (MTSingle x) (MTSingle y) MTNeutral = rfl {c}
  plusAssoc (MTSingle x) (MTSingle y) (MTSingle z) = plusAssoc x y z

instance MySemigroup c => MyMonoid (MonoidTerm c) where
  Neutral = MTNeutral

  neutralLeftNeutral MTNeutral = ()
  neutralLeftNeutral (MTSingle x) = rfl {c}
  neutralRightNeutral MTNeutral = ()
  neutralRightNeutral (MTSingle x) = rfl {c}

MonMag : Type -> Type
MonMag a = FreeMagma (MonoidTerm a)

{-
instance Set c => Set (MonMag c) where
  (~=) (MkMonMag x) y = ?heou_1
  rfl = ?oaoo
  symm = ?oueoaee
  trns = ?mmkehco
  -}


exprToMonMag : MonoidExpr a -> MonMag a
exprToMonMag NeutralE = MagSingle MTNeutral
exprToMonMag (MonSingle x) = MagSingle (MTSingle x)
exprToMonMag (MonPlus x y) = MagPlus (exprToMonMag x) (exprToMonMag y)

canonMon'' : Set c => FreeMagma (MonoidTerm c) -> MonoidTerm (FreeMagma c)
canonMon'' {c} q =
  let foo : (MonoidTerm c -> MonoidTerm (FreeMagma c))
          = map MagSingle
      bar = fmSplit {c=MonoidTerm c} {n=MonoidTerm (FreeMagma c)} foo
  in bar q


{-
How does the `map MagSingle` fit into proving things?

                          c   --MTSingle-->  MonoidTerm c   --MagSingle-->   FreeMagma (MonoidTerm c)
                                                                             /
                                                 |                        /
                                              map MagSingle         canonMon''
                                                 |                  /
                                                 v                /
c   --MagSingle--> FreeMagma c --MTSingle--> MonoidTerm (FreeMagma c)
-}
