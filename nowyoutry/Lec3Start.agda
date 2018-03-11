{-# OPTIONS --type-in-type #-}  -- yes, there will be some cheating in this lecture

module Lec3Start where

open import Lec1Done
open import Lec2Done

postulate
  -- Two functions are the same if they both send the same inputs to
  -- the same outputs.  This is different from the structural equality (==),
  -- which says that two things are the same if they have the same definition
  -- (structure).  Extensionality is handy when we know that two things are
  -- equal, but they are just defined differently.
  -- The name essentially means that the behavior is deteremined
  -- by external things (inputs).
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x == g x) ->
                   f == g

record Category : Set where
  field

    -- two types of thing
    Obj  : Set                  -- "objects"
    _~>_ : Obj -> Obj -> Set    -- "arrows" or "morphisms"
                                -- or "homomorphisms"
                
    -- two operations
    id~>        : {T : Obj} ->      T ~> T
    _>~>_       : {R S T : Obj} ->  R ~> S  ->  S ~> T  ->  R ~> T

    -- three laws
    law-id~>>~> : {S T : Obj}     (f : S ~> T) ->
                    (id~> >~> f) == f
    law->~>id~> : {S T : Obj}     (f : S ~> T) ->
                    (f >~> id~>) == f
    law->~>>~>  : {Q R S T : Obj} (f : Q ~> R)(g : R ~> S)(h : S ~> T) ->
                    ((f >~> g) >~> h) == (f >~> (g >~> h))

-- Sets and functions are the classic example of a category.
SET : Category
SET = record
        { Obj = Set  -- objects are Sets
        ; _~>_ = \ S T -> S -> T -- arrows are functions between Sets
        ; id~> = id  -- the identity arrow is the identity function
        ; _>~>_ = \ f g -> f >> g  -- arrow composition is function composition
        ; law-id~>>~> = \ f -> refl f
        ; law->~>id~> = \ f -> refl f
        ; law->~>>~> = \ f g h -> refl \ x -> h (g (f x))
        }

-- All proofs of a given inequality are equal.
-- Or: two differently expressed proofs of the same inequality are
-- the same proof.
unique->= : (m n : Nat)(p q : m >= n) -> p == q
-- m >= n matches on the second argument, so we start by deconstructing it:
unique->= m zero <> <> = refl <>
-- We then pattern match on the first argument:
-- In this case, both arguments are nonsense, but only one is
-- substituted automatically after a case split:
unique->= zero (suc n) () ()
-- Then, use the induction hypothesis:
unique->= (suc m) (suc n) p q = unique->= m n p q

-- A PREORDER is a category where there is at most one arrow between
-- any two objects. (So arrows are unique.)
NAT->= : Category
NAT->= = record
           { Obj = Nat  -- objects are natural numbers
           ; _~>_ = _>=_  -- arrows are the >= operation (proofs that
                          -- they are greater than or equal to)
           ; id~> = \ {n} -> refl->= n  -- >= is reflexive: n >= n
           -- >= is transitive: x >= y -> y >= z -> x >= z
           ; _>~>_ = \ {r s t} r>=s s>=t -> trans->= r s t r>=s s>=t
           -- The laws are solved by passing 'unique' and hitting 'auto'.
           -- The proofs are easy because >= is defined in terms of
           -- Zero and One, which are trivial.
           ; law-id~>>~> = \ {S T} f -> unique->= S T (trans->= S S T (refl->= S) f) f
           ; law->~>id~> = \ {S T} f -> unique->= S T (trans->= S T T f (refl->= T)) f
           ; law->~>>~> = \ {Q R S T} f g h ->
                              unique->= Q T (trans->= Q S T (trans->= Q R S f g) h)
                              (trans->= Q R T f (trans->= R S T g h))
           }

-- A MONOID is a category with Obj = One.
-- The values in the monoid are the *arrows*.
ONE-Nat : Category
ONE-Nat = record
            { Obj = One  -- there's only one object
            -- The arrows are natural numbers (the number of times
            -- for getting from here to here).
            ; _~>_ = \ One One -> Nat
            -- Is there an identity natural number?
            -- Yes, zero is the identity with respect to addition.
            -- Another option is one: the identity with respect to
            -- multiplication.
            ; id~> = zero
            -- So we pick the appropriate operation with respect to
            -- the identity element:
            ; _>~>_ = _+N_
            -- The laws are the monoid laws:
            ; law-id~>>~> = zero-+N
            ; law->~>id~> = +N-zero
            ; law->~>>~> = assocLR-+N
            }

eqUnique : {X : Set}{x y : X}(p q : x == y) -> p == q
eqUnique (refl x) (refl .x) = refl (refl x)

-- A DISCRETE category is one where the only arrows are the identities.
-- Every set can be turned into a discrete category on that Set.
-- In this diagram, there's no arrows between dots.  There are only
-- dots and arrows pointing to the same dots (the identity arrows).
DISCRETE : (X : Set) -> Category
DISCRETE X = record
               { Obj = X  -- objects are the elements of the Set
               ; _~>_ = _==_ -- arrows are the equality proofs between the objects
               ; id~> = \ {x} -> refl x -- everything is equal to itself
               -- Equality is transitive:
               -- (Note the pattern-matching lambda.)
               ; _>~>_ =  \ { (refl x) (refl .x) -> refl x }
               -- Typing 'eqUnique' into the holes and doing 'auto' solves these,
               -- but Agda is not happy about the code it generates,
               -- hence the underscores.  This works out in the end because of how
               -- equality is defined (the same object on both sides).
               ; law-id~>>~> = \ _ -> eqUnique _ _
               ; law->~>id~> = \ _ -> eqUnique _ _
               ; law->~>>~> = \ _ _ _ -> eqUnique _ _
               }



-- Not to be confused with the Functor from Haskell.  This one is more general.
--
-- FUNCTOR example: railway map vs the actual railway.
-- * dots on the map correspond to railway stations
-- * lines on the map correspond to the actual tracks.
--
-- Note: there could be more objects and arrows in the target category.
module FUNCTOR where
  -- When you define the record structure, the fields are not automatically
  -- brought into scope.  Because sometimes they can be used as projection
  -- functions or field values if you work with a single record.
  --
  -- In other words, if you open the record type, you get the
  -- projections, and if you open the record value, you get the
  -- values.
  --
  -- So, this gives the projections (locally to the FUNCTOR
  -- module because it might be undesirable to have them as projections
  -- everywhere):
  open Category

  record _=>_ (C D : Category) : Set where  -- "Functor from C to D"
    field
      -- Two actions:
      -- 1) map objects of the source category C to objects of the
      -- target category D:
      F-Obj : Obj C -> Obj D
      -- 2)
      -- If we got an arrow in the source category C between S and T,
      -- there should be an arrow in the target category D between wherever
      -- the objects get mapped to:
      F-map : {S T : Obj C} -> _~>_ C S T -> _~>_ D (F-Obj S) (F-Obj T)

      -- Two laws:
      -- 1) identity arrows of the source category C must be sent to identity
      -- arrows of the target category D:
      F-map-id~> : {T : Obj C} -> F-map (id~> C {T}) == id~> D {F-Obj T}
      -- 2) if you compose in the source category C and map the result of that
      -- composition to the target category D, you should get the same thing
      -- as if you first map over the target category D and compose there.
      F-map->~>  : {R S T : Obj C}(f : _~>_ C R S)(g : _~>_ C S T) ->
                     F-map (_>~>_ C f g) == _>~>_ D (F-map f) (F-map g)

-- Bring _=>_ into scope (without bringing stuff from Category because
-- that import is not public).
open FUNCTOR

VEC : Nat -> SET => SET
VEC n = record
  -- Objects in the category of Sets (SET) are Sets.
  -- C-u C-u C-c C-, (or C-.) is useful here to normalize the types fully.
  { F-Obj = \ X -> Vec X n -- map a Set of elements to a Set of vectors
  ; F-map = vmap
  ; F-map-id~> = extensionality vmap-id
  ; F-map->~> = \ f g -> extensionality (vmap->~> f g)
  }
  where
    vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
    vmap f [] = []
    vmap f (x ,- v) = f x ,- vmap f v

    vmap-id : forall {n T} (x : Vec T n) -> vmap (\ e -> e) x == x
    vmap-id [] = refl []
    vmap-id (x ,- xs) rewrite vmap-id xs = refl (x ,- xs)

    vmap->~> : forall {n R S T} (f : R -> S) (g : S -> T) (x : Vec R n) ->
                 vmap (\ y -> g (f y)) x == vmap g (vmap f x)
    vmap->~> _ _ [] = refl []
    vmap->~> f g (x ,- xs) rewrite vmap->~> f g xs
      = refl (g (f x) ,- vmap g (vmap f xs))


VTAKE : Set -> NAT->= => SET
VTAKE X = record
  -- Maps a number to a vector that long and whose elements live in X.
  { F-Obj = Vec X  -- Nat -> Set
  ; F-map = \ {m n} m>=n xs -> vTake m n m>=n xs
  ; F-map-id~> = \ {n} -> extensionality (vTakeIdFact n)
  ; F-map->~> = \ {r s t} f g -> extensionality (vTakeCpFact r s t f g)
  }

-- So this functor just adds 'd' to all the numbers of the source
-- NAT->= such that the target category respects all the >=
-- relationships as before.
--
-- Example:
-- If d == 2:
--
-- SRC:             TGT:
-- 3 ~> 5 ~> 8       5 ~> 7 ~> 10
--  \        ^   =>   \        ^
--   \~~~~~~/          \~~~~~~/
ADD : Nat -> NAT->= => NAT->=
ADD d = record
  { F-Obj = d +N_ -- Nat -> Nat
  ; F-map =  \ {m n} -> dmap d m n
  -- Automatically generated by passing 'unique->=' to 'auto'.
  ; F-map-id~> = λ {T} →
                     unique->= (d +N T) (d +N T) (dmap d T T (refl->= T))
                     (refl->= (d +N T))
  ; F-map->~> = λ {R} {S} {T} f g →
                    unique->= (d +N R) (d +N T) (dmap d R T (trans->= R S T f g))
                    (trans->= (d +N R) (d +N S) (d +N T) (dmap d R S f) (dmap d S T g))
  }
{-
  -- Written manually:
  ; F-map-id~> = \ {n} -> dmap-id d n
  ; F-map->~> = \ {r s t} f g -> dmap->~> d r s t f g
  }
-}
  where
    -- Using helper functions to prove by induction (we need a name to refer
    -- to itself, so a lambda won't do it, even with pattern matching).
    dmap : (d m n : Nat) -> m >= n -> (d +N m) >= (d +N n)
    dmap zero m n m>=n = m>=n
    dmap (suc d) m n m>=n = dmap d m n m>=n
{-

    dmap-id : (d n : Nat) -> dmap d n n (refl->= n) == refl->= (d +N n)
    dmap-id zero n = refl (refl->= n)
    dmap-id (suc d) n = dmap-id d n

    dmap->~> : (d r s t : Nat) (f : r >= s) (g : s >= t) ->
               dmap d r t (trans->= r s t f g) ==
                 trans->= (d +N r) (d +N s) (d +N t) (dmap d r s f) (dmap d s t g)
    dmap->~> zero r s t f g = refl (trans->= r s t f g)
    dmap->~> (suc d) r s t f g = dmap->~> d r s t f g
-}


CATEGORY : Category
CATEGORY = record
             { Obj = Category  -- objects are categories
             ; _~>_ = _=>_  -- arrows are functors (that's how to get from one
                            -- category to another)
             ; id~> = record
               { F-Obj = id
               ; F-map = id
               -- Agda doesn't like what 'auto' derives:
               -- Invalid dotted expression
               -- when checking that the expression .T has type Category
               -- ; F-map-id~> = λ {T} → refl (Category.id~> .T)
               ; F-map-id~> = \ {T} -> refl _
               -- ; F-map->~> = λ {R} {S} {T} f g → refl ((.T Category.>~> f) g)
               ; F-map->~> = \ {R} {S} {T} f g → refl _
               }
             ; _>~>_ = \ F G -> record
               { F-Obj = F-Obj F >> F-Obj G
               ; F-map = F-map F >> F-map G
               ; F-map-id~> = \ {T} -> {!?!}
               ; F-map->~> = {!!}
               }
             ; law-id~>>~> = {!!}
             ; law->~>id~> = {!!}
             ; law->~>>~> = {!!}
             } where open _=>_
