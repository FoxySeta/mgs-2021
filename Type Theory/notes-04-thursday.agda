-- notes-04-thursday.agda

open import mylib

{-
  Infinite datastructure
  - streams, Stream A
  0 ,1 , 2 ,3 ,4, ... : Stream ℕ
  1, 1 , 2, 3 ,5 ,..
  2, 3, 5, 7, 11,..

  duality, categorical mirror
  _×_ (products) and _⊎_ (coproducts, sums)

  Inductive datatypes: finite datastructures
  Coinductive datatypes: Streams, ℕ∞ (conatural numbers)
-}

record Stream (A : Set) : Set where
  constructor _∷_
  coinductive
  field
    head : A
    tail : Stream A

open Stream

{-
  _∷S_ : A → Stream A → Stream A
  head (a ∷S as) = a
  tail (a ∷S as) = as
-}

from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n)

-- from is productive because it is guarded

mapS : (A → B) → Stream A → Stream B
head (mapS f as) = f (head as)
tail (mapS f as) = mapS f (tail as)

{-
  filterS : (A → Bool) → Stream A → Stream A
  head (filterS f as) = if f (head as) then (head as) else {!!}
  tail (filterS f as) = {!!} -- no guarded definition of filter
-}

-- Conatural numbers

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

-- Maybe A = 1 ⊎ A

pred : ℕ → Maybe ℕ
pred zero = nothing
pred (suc n) = just n

zero-suc : Maybe ℕ → ℕ
zero-suc nothing = zero
zero-suc (just n) = suc n
-- Lambek's lemma, initial algebras

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞
-- terminal coalgebra

-- emb : ℕ → ℕ∞ -- 2 ways
-- f : ℕ∞ → ℕ -- no way, cons local continuity

open ℕ∞

zero∞ : ℕ∞
pred∞ zero∞ = nothing

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ n) = just n

∞ : ℕ∞
pred∞ ∞ = just ∞

{-
  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  suc m + n = suc (m + n)
-}

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m +∞ n) with pred∞ m
... | nothing = pred∞ n
... | just m' = just (m' +∞ n)

{-
  Dependent types (families)
  A dependent type is a function whose codomain is Set.
  List : Set → Set
  Not proper?

  Vec : Set → ℕ → Set
  Vec A n = tuple of n as
  { as | length as = n} -- type theoretic of comprehension

  Fin : ℕ → Set
  Fin n = a set with n elements
  {0 , 1, .. , n-1}

  Function type
  A B : Set 
  A → B : Set

  Dependent function type (Π-type)
  A : Set
  B : A → Set

  (x : A) → B x
  {x : A} → B x -- hidden arguments

  zeros : (n : ℕ) → Vec ℕ n

-}

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

zeros : (n : ℕ) → Vec ℕ n
zeros zero = []
zeros (suc n) = 0 ∷ zeros n

{-
_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
-}

_++v_ : {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++v ys = ys
(x ∷ xs) ++v ys = x ∷ (xs ++v ys)

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

{-
  Fin 0 = {}
  Fin 1 = { zero{0} }
  Fin 2 = { zero{1} , suc{1} (zero{0}) }
  ...
-}

_!!_ : {n : ℕ} → Vec A n → Fin n → A -- safe lookup function
(a ∷ as) !! zero = a
(a ∷ as) !! suc n = as !! n
