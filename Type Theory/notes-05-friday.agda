-- notes-05-friday.agda

open import mylib

-- Π-types = dependent function types
Π : (A : Set)(B : A → Set) → Set
Π A B = (x : A) → B x

syntax Π A (λ x → P)  = Π[ x ∈ A ] P

-- Σ-types = dependent pair type

record Σ(A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

syntax Σ A (λ x → P)  = Σ[ x ∈ A ] P

List' : Set → Set
List' A = Σ[ n ∈ ℕ ] Vec A n

List'' : Set → Set -- ex: show that this is isomorphic to lists
List'' A = Σ[ n ∈ ℕ ] Fin n → A

{-
  Container representation of lists.
  Set of shapes S = ℕ.
  Family of positions P : ℕ → Set, P = Fin.
  All strictly positive types can be represented as containers ( ~ polynomial
  functors) !
-}

{-
A → B = Π[ _ ∈ A ] B
A × B = Σ[ _ ∈ A ] B
-}

_⊎'_ : Set → Set → Set
A ⊎' B = Σ[ b ∈ Bool ] F b
         where F : Bool → Set
               F true = A
               F false = B

_×'_ : Set → Set → Set -- exercise: show that this equivalent to ⊎
A ×' B = Π[ b ∈ Bool ] F b
         where F : Bool → Set
               F true = A
               F false = B

{-
  "Propositions as types": for predicate logic
  P : A → prop = dependent type
-}

All : (A : Set)(P : A → prop) → prop
All A P = Π[ x ∈ A ] P x

Ex : (A : Set)(P : A → prop) → prop
Ex A P = Σ[ x ∈ A ] P x

syntax All A (λ x → P)  = ∀[ x ∈ A ] P  
infix 0 All
syntax Ex A (λ x → P) = ∃[ x ∈ A ] P
infix 0 Ex

variable PP QQ : A → prop

taut : (∀[ x ∈ A ] PP x ⇒ Q) ⇔ (∃[ x ∈ A ] PP x) ⇒ Q
proj₁ taut f (a , pa) = f a pa
proj₂ taut g a pa = g (a , pa)

data _≡_ : A → A → prop where
  refl : {a : A} → a ≡ a

infix 4 _≡_

-- inductive definition of equality: _≡_ is an equivalence relation

sym : (a b : A) → a ≡ b → b ≡ a
sym a .a refl = refl

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

cong : {a b : A}(f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

{-
  Proving that + is associative

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n) 
-}

assoc : (i j k : ℕ) → (i + j) + k ≡ i + (j + k)
assoc zero j k = refl
assoc (suc i) j k = cong suc (assoc i j k)

-- proof by induction = pattern matching + recursion

ind : (P : ℕ → Set)
    → P 0
    → ((n : ℕ) → P n → P (suc n))
    → (n : ℕ) → P n
ind P z s zero = z
ind P z s (suc n) = s n (ind P z s n)

-- eliminator for ℕ = induction/dependent recursion

{-
data _≡_ : A → A → prop where
  refl : {a : A} → a ≡ a

  What is ind for equality?
-}

ind≡ : (P : (a b : A) → a ≡ b → prop)
       (r : (a : A) → P a a refl)
       → (a b : A)(p : a ≡ b) → P a b p
ind≡ P r a .a refl = r a

-- Ex. derive sym, trans, cong from ind≡ (= J)

uip : (a b : A)(p q : a ≡ b) → p ≡ q
uip = ind≡ (λ a b p → (q : a ≡ b) → p ≡ q) λ a q →
           {!!}
--uip refl refl = refl

{-
  Is uip derivable from J ? Hofmann & Streicher: groupoid model of type theory.
  Restricted version of HoTT (infinity groupoid model of TT); observed: version
  of univalence in this theory. Voevodsky formulated HoTT, which supports full
  univalence.
-}
