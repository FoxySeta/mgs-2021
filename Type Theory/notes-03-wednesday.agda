-- notes-03-wednesday.agda

open import mylib

{-
  Classical vs intuitionistic logic 
  In classical logica, we assume that each proposition is either true or false.
  Excluded middle, tertium non datur (the third is not given).
  To prove P, assume not P and derive a contradiction: indirect proof, reduction
  ad absurdum, reduction to the absurd.

-}

TND : prop → prop
TND P = P ∨ ¬ P

deMorgan' : TND P → ¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q
proj₁ (deMorgan' (inj₁ p)) h = inj₂ (λ q → h (p , q))
proj₁ (deMorgan' (inj₂ np)) h = inj₁ np
proj₂ (deMorgan' tnd) (inj₁ np) (p , q) = np p
proj₂ (deMorgan' _)  (inj₂ nq) (p , q) = nq q

RAA : prop → prop
RAA P = ¬ ¬ P → P

tnd→raa : TND P → RAA P
tnd→raa (inj₁ p) nnp = p
tnd→raa (inj₂ np) nnp = case⊥ (nnp np)

{-
raa→tnd : RAA P → TND P
is not provable.
-}

nntnd : ¬ ¬ (P ∨ ¬ P)
nntnd h = h (inj₂ (λ p → h (inj₁ p)))

raa→tnd : ({P : prop} → RAA P) → {Q : prop} → TND Q
raa→tnd raa = raa nntnd

{-
  Datatypes, infinite types
  ℕ - natural numbers, Peano 
  Every natural number is either 0 or a successor of a number.
  Peano arithmetic.
-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

one : ℕ
one = suc zero

two : ℕ
two = suc one

{-# BUILTIN NATURAL ℕ #-}

fifteen : ℕ
fifteen = 15

infixl 2 _+_
_+_ : ℕ → ℕ → ℕ -- structural recursive definition 
zero + n = n
suc m + n = suc (m + n)

infixl 4 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = 0
suc m * n = m * n + n

data List (A : Set) : Set where
  [] : List A -- nil
  _∷_ : A → List A → List A -- cons

-- ℕ = List ⊤

_++_ : List A → List A → List A -- append
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- _++'_ : List A \to List B \to List (A \vee B)?

-- recursive but not inductive
{-# NO_POSITIVITY_CHECK #-}
data Λ : Set where
  lam : (Λ → Λ) → Λ

app : Λ → Λ → Λ
app (lam f) x = f x

self-apply : Λ
self-apply = lam λ x → app x x

Ω : Λ
Ω = app self-apply self-apply
-- normalisation doesn't terminate

data Ord : Set where
  zero : Ord
  suc : Ord → Ord
  lim : (ℕ → Ord) → Ord

-- strictly positive

{-# NO_POSITIVITY_CHECK #-}
data Reynolds : Set where
  inn : ((Reynolds → Bool) → Bool) → Reynolds

{-
  Inconsistent with classical logic
  It doesn't adhere to the intuitionistic explanation of inductive datatypes.
  Hence we reject types like this.
  - strictly positive = recursive type only appears on the right of an arrow
    type.
  - strictly positive = container / polynomial functors.
-}
