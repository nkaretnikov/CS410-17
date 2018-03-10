module Lec2Start where

open import Lec1Done


------------------------------------------------------------------------------
-- Vectors  -- the star of exercise 1
------------------------------------------------------------------------------

data Vec (X : Set) : Nat -> Set where  -- like lists, but length-indexed
  []   :                              Vec X zero
  _,-_ : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
infixr 4 _,-_   -- the "cons" operator associates to the right


------------------------------------------------------------------------------
-- Taking a Prefix of a Vector
------------------------------------------------------------------------------

vTake : (m n : Nat) -> m >= n -> {X : Set} -> Vec X m -> Vec X n
vTake m zero m>=n xs = []
vTake zero (suc n) () xs
vTake (suc m) (suc n) m>=n (x ,- xs) = x ,- vTake m n m>=n xs

------------------------------------------------------------------------------
-- Things to Prove
------------------------------------------------------------------------------

vTakeIdFact : (n : Nat){X : Set}(xs : Vec X n) ->
              vTake n n (refl->= n) xs == xs
vTakeIdFact zero [] = refl []
-- vTakeIdFact (suc n) (x ,- xs) rewrite vTakeIdFact n xs = refl (x ,- xs)
--
-- How rewrite works:
-- * introduce a new variable 'z' and bind it to the first expression in 'with'
-- * use 'z' in the context and goal
-- * use the proof that 'z == xs' to establish that 'z' and 'xs' are the same
-- * rewrite the goal accordingly.
--
-- In fact, it should have been enough just to use 'with VTakeIdFact n
-- xs', but Agda refuses to use that because 'xs' appears on both
-- sides of the equality.  By binding 'vTake n n (refl->= n) xs' (the
-- LHS of the said equality) to 'z', this problem gets solved.  And by
-- pattern matching on the proof, we see that 'z' is in fact 'xs'.
vTakeIdFact (suc n) (x ,- xs) with vTake n n (refl->= n) xs | vTakeIdFact n xs
vTakeIdFact (suc n) (x ,- xs) | .xs | refl .xs = refl (x ,- xs)

vTakeCpFact : (m n p : Nat)(m>=n : m >= n)(n>=p : n >= p)
              {X : Set}(xs : Vec X m) ->
              vTake m p (trans->= m n p m>=n n>=p) xs ==
                vTake n p n>=p (vTake m n m>=n xs)
{- hit p first: why? -}                
vTakeCpFact m n zero m>=n n>=p xs = refl []
vTakeCpFact m zero (suc p) m>=n () xs
vTakeCpFact zero (suc n) (suc p) () n>=p xs
vTakeCpFact (suc m) (suc n) (suc p) m>=n n>=p (x ,- xs)
-- Same story here, couldn't just 'rewrite', so ended up using two 'with'es:
  with vTake m p (trans->= m n p m>=n n>=p) xs
    | vTakeCpFact m n p  m>=n n>=p xs
vTakeCpFact (suc m) (suc n) (suc p) m>=n n>=p (x ,- xs)
    | .(vTake n p n>=p (vTake m n m>=n xs))
    | refl .(vTake n p n>=p (vTake m n m>=n xs))
    = refl (x ,- vTake n p n>=p (vTake m n m>=n xs))

------------------------------------------------------------------------------
-- Splittings (which bear some relationship to <= from ex1)
------------------------------------------------------------------------------

data _<[_]>_ : Nat -> Nat -> Nat -> Set where
  zzz : zero <[ zero ]> zero
  lll : {l m r : Nat} ->      l <[     m ]> r
                      ->  suc l <[ suc m ]> r
  rrr : {l m r : Nat} ->      l <[     m ]>     r
                      ->      l <[ suc m ]> suc r

-- The order of cases is important here for writing 'findSplit'.
-- Agda matches on the leftmost pattern that is a constructor, so we
-- make the 'rrr' case first to make it match on the second pattern.
_>[_]<_ : {X : Set}{l m r : Nat} ->
          Vec X l -> l <[ m ]> r -> Vec X r ->
          Vec X m
xl        >[ rrr nnn ]< (x ,- xr) = x ,- (xl >[ nnn ]< xr)
[]        >[ zzz ]<     []        = []
(x ,- xl) >[ lll nnn ]< xr        = x ,- (xl >[ nnn ]< xr)

-- Given a list of instructions 'nnn' for a vector 'xs', _there exist_
-- vectors 'xl' and 'xr' _such that_ 'xs' can be constructed from them
-- using the same instructions.  In other words, constructing 'xs'
-- from 'xl' and 'xr' should be the exact opposite of deconstructing
-- 'xs' into 'xl' and 'xr', using the same instructions.
data FindSplit {X : Set}{l m r : Nat}(nnn : l <[ m ]> r)
     : (xs : Vec X m) -> Set where
  splitBits : (xl : Vec X l)(xr : Vec X r) -> FindSplit nnn (xl >[ nnn ]< xr)

findSplit : {X : Set}{l m r : Nat}(nnn : l <[ m ]> r)(xs : Vec X m) ->
            FindSplit nnn xs
findSplit zzz [] = splitBits [] []
findSplit (lll nnn) (x ,- xs) with findSplit nnn xs
-- By pattern matching on the result of the recursive call, we get to know that
-- xs is in fact made of xl and xr:
findSplit (lll nnn) (x ,- .(xl >[ nnn ]< xr)) | splitBits xl xr
-- Automation doesn't do much here, you basically have to write down the result
-- yourself (by making sense of the goal type).
-- 'lll' in the goal suggests that 'x' should go into the left vector:
-- Goal: FindSplit (lll nnn) (x ,- (xl >[ nnn ]< xr))
  = splitBits (x ,- xl) xr
-- Same approach:
-- findSplit (rrr nnn) (x ,- xs) with findSplit nnn xs
-- findSplit (rrr nnn) (x ,- .(xl >[ nnn ]< xr)) | splitBits xl xr
--   = splitBits xl (x ,- xr)
--
-- Or, to look into how 'with' works, use a helper function by typing
-- some name into the hole (like 'help', but that would make arguments
-- implicit, so it's better to provide them: 'help nnn x xs') and calling
-- 'agda2-helper-function-type', which copies the output into the
-- clipboard.
--
-- The 'help' function will have the context as its arguments.
--
-- Next, we'll probably have to do a recursive call on 'findSplit nnn xs',
-- but instead of using 'with', we'll make it an argument of the
-- helper function.  (We can grab its type by typing 'findSplit nnn
-- xs' into the hole and use 'agda2-goal-and-context-and-inferred',
-- which gives us 'FindSplit nnn xs'.
--
-- This basically adds 'rc' to the context we had before.
--
-- Then, we pattern match on 'rc', which establishes that 'xs' is
-- equal to 'xl >[ nnn ]< xr'.
--
-- And we give back the result manually as before.  'rrr' in the goal suggests
-- that 'x' should go to the right vector:
-- Goal: FindSplit (rrr nnn) (x ,- (xl >[ nnn ]< xr))
findSplit (rrr nnn) (x ,- xs) = help nnn x xs (findSplit nnn xs)
  where
    help : forall {m l r X} (nnn : l <[ m ]> r) (x : X) (xs : Vec X m) ->
        (rc : FindSplit nnn xs) -> FindSplit (rrr nnn) (x ,- xs)
    help nnn x .(xl >[ nnn ]< xr) (splitBits xl xr) = splitBits xl (x ,- xr)



------------------------------------------------------------------------------
-- what I should remember to say
------------------------------------------------------------------------------

-- What's the difference between m>=n and m >= n ?
   {- m>=n (without spaces) is just an identifier; it could be anything,
      but it has been chosen to be suggestive of its *type* which is
      m >= n (with spaces) which is the proposition that m is at least n.
      By "proposition", I mean "type with at most one inhabitant", where
      we care more about whether there is an inhabitant or not than which
      one (because there's never a choice). Finished code does not show
      us the types of its components, and that's not always a good thing.
      Here, by picking nice names, we get something of an aide-memoire. -}

-- What does (x ,-_) mean?
   {- It's a "left section". Right sections (_,- xs) also exist sometimes.
      Why only sometimes? -}

-- "Why is it stuck?"
   {- Proof by induction isn't just flailing about, you know? The trick is
      to pick the case analysis that provokes the "stuck" programs to do a
      step of computation. Then the same reasoning that justifies the
      termination of the program will justify the induction in a proof
      about it. -}
      
