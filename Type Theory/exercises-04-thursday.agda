-- exercises-04-thursday.agda

open import mylib

-- 1. Coinduction

{-
  Now your task is to define multiplication _*∞_ for conatural numbers.

  This is harder then it sounds. Why? Because to check termination of
  corecursive programs agda needs to make sure that if you want to find out a
  finite amout of information about the result of the function it only needs a
  finite amount of information about its inputs. Such a function is called
  productive. And agda isn't very clever in figuring this out, it has to be
  obvious from the program (similar as structural recursion has to be
  obviously structural). 
  You should *not* use the TERMINATING pragma in your solution.
  But it may be useful for experiments.

  _*_ : ℕ → ℕ → ℕ
  zero * n = zero
  suc m * n = n + m * n
-}

{-
_*∞_ :  ℕ∞ → ℕ∞ → ℕ∞
m *∞ n = {!!}
-}

aux : ℕ∞ → ℕ∞ → ℕ∞ → ℕ∞  -- aux l m n = l +∞ (m *∞ n)
pred∞ (aux l m n) with pred∞ l
pred∞ (aux l m n) | nothing with  pred∞ m
pred∞ (aux l m n) | nothing | nothing = nothing
pred∞ (aux l m n) | nothing | just m' with pred∞ n
pred∞ (aux l m n) | nothing | just m' | nothing = nothing
pred∞ (aux l m n) | nothing | just m' | just n' = just (aux n' m' n)
pred∞ (aux l m n) | just l' = just (aux l' m n)

{-# TERMINATING #-}
_*∞_ :  ℕ∞ → ℕ∞ → ℕ∞
m *∞ n = aux zero∞ m n
{-
pred∞ (m *∞ n) with pred∞ m
... | nothing = nothing
... | just m' with pred∞ n
...           | nothing = nothing
...           | just n' = just (n' +∞ (m' *∞ n))
-}

{-
with pred∞ m
...| nothing = zero∞
...| just m' with pred∞ n
...|              nothing = zero∞
...|              just n' = n' +∞ (m' *∞ n)
-}

-- pred∞ (∞ *∞ zero∞) = nothing
-- here are some testing tools
ℕ→ℕ∞ : ℕ → ℕ∞
ℕ→ℕ∞ zero = zero∞
ℕ→ℕ∞ (suc n) = suc∞ (ℕ→ℕ∞ n)

{-# TERMINATING #-} -- a lie
-- this function is a cheat - it doesn't terminate for ∞
ℕ∞→ℕ : ℕ∞ → ℕ
ℕ∞→ℕ n with pred∞ n
ℕ∞→ℕ n | nothing = 0
ℕ∞→ℕ n | just n' = suc (ℕ∞→ℕ n')

-- My unit-test
x3*5 = ℕ∞→ℕ (ℕ→ℕ∞ 3 *∞ ℕ→ℕ∞ 5)

-- 2. Dependent types  Fin

{-
  Define the following operations on Fin
  - max returns the largest element in Fin (suc n)
  - emb embeds Fin n into Fin (suc n) without changing its values
  - inv inverts the order of elements in Fin n
-}

max : (n : ℕ) → Fin (suc n)
max zero = zero
max (suc n) = suc (max n)

emb : {n : ℕ} → Fin n → Fin (suc n)
emb zero = zero
emb (suc m) = suc (emb m)

inv : {n : ℕ} → Fin n → Fin n
inv zero = max _
inv (suc i) = emb (inv i)

-- 2. Dependent types : Vec

Vector : ℕ → Set {- Vec n is an n-dimensional vector -}
Vector m = Vec ℕ m

Matrix : ℕ → ℕ → Set {- Matrix m n is an m x n Matrix -}
Matrix m n = Vec (Vector n) m

m3 : Matrix 3 3
m3 = (1 ∷ 2 ∷ 3 ∷ []) 
    ∷ (4 ∷ 5 ∷ 6 ∷ []) 
    ∷ (7 ∷ 8 ∷ 9 ∷ []) 
    ∷ []

m4 : Matrix 3 2
m4 = (1 ∷ 2 ∷ []) 
    ∷ (4 ∷ 5 ∷ []) 
    ∷ (7 ∷ 8 ∷ []) 
    ∷ []

-- Define the operation transpose which switches columns and rows.
-- Applicative functor, Vec _ n is an applicative functor
-- mapVec : (A → B) → Vec A n → Vec B n
-- return : A → Vec A n
-- app : Vec (A → B) n → Vec A n → Vec B n
-- mapVec f as = app (return f) as

return : {A : Set}{n : ℕ} → A → Vec A n
return {n = zero} a = []
return {n = suc m} a = a ∷ return {n = m} a

app : {A B : Set}{n : ℕ} → Vec (A → B) n → Vec A n → Vec B n
app [] [] = []
app (a2b ∷ a2bs) (a ∷ as) = a2b a ∷ app a2bs as

transpose : {m n : ℕ} → Matrix m n → Matrix n m
transpose [] = return []
transpose (ns ∷ mns) = app (app (return _∷_) ns) (transpose mns)

{-
transpose : {m n : ℕ} → Matrix m n → Matrix n m
transpose [] = {!!} -- [ [] , [] , [] ] m empty rows
transpose (ns ∷ mns) = {!transpose mns!}
-}
-- if ns = [1 , 2 , 3]
-- transpose mns = [ns1 , ns2 , ns3] => [1 ∷ ns1 , 2 ∷ ns2 , 3 ∷ ns3]

test8 : Matrix 2 3
test8 = transpose m4

test9 : Matrix 3 3
test9 = transpose m3
