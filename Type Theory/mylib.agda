{- small library for MGS 2021 -}

{- products and sums -}

infix 10 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

variable
  A B C M : Set

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b) -- C-c C-,
uncurry : (A → B → C) → (A × B → C)
uncurry f (a , b) = f a b

infix 5 _⊎_
data _⊎_(A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case : (A → C) → (B → C) → (A ⊎ B → C)
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

uncase : (A ⊎ B → C) → (A → C) × (B → C)
uncase f = (λ a → f (inj₁ a)) , λ b → f (inj₂ b)

--case' : (A → C) × (B → C) → (A ⊎ B → C)
--case' = uncurry case

record ⊤ : Set where
  constructor tt

open ⊤ public

data ⊥ : Set where

case⊥ : ⊥ → A
case⊥ ()

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : Bool → A → A → A
if true then x else y = x
if false then x else y = y

{- bool logic -}

_&_ : Bool → Bool → Bool
true & y = y
false & y = false

{- ∣ = \mid -}

_∣_ : Bool → Bool → Bool
true ∣ y = true
false ∣ y = y

!_ : Bool → Bool
! true = false
! false = true

_⇒b_ : Bool → Bool → Bool
true ⇒b y = y
false ⇒b y = true

{- prop logic -}

prop = Set

variable
  P Q R : prop

infix 3 _∧_
_∧_ : prop → prop → prop
P ∧ Q = P × Q

infix 2 _∨_
_∨_ : prop → prop → prop
P ∨ Q = P ⊎ Q

infixr 1 _⇒_
_⇒_ : prop → prop → prop
P ⇒ Q = P → Q

False : prop
False = ⊥

True : prop
True = ⊤

¬_ : prop → prop
¬ P = P ⇒ False

infix 0 _⇔_
_⇔_ : prop → prop → prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

efq : False ⇒ P
efq = case⊥

{- classical principles -}

TND : prop → prop
TND P = P ∨ ¬ P

RAA : prop → prop
RAA P = ¬ ¬ P ⇒ P

tnd⇒raa : TND P ⇒ RAA P
tnd⇒raa (inj₁ p) nnp = p
tnd⇒raa (inj₂ np) nnp = efq (nnp np)

nnpnp : ¬ ¬ (P ∨ ¬ P)
nnpnp h = h (inj₂ (λ p → h (inj₁ p)))

raa⇒tnd : RAA (P ∨ ¬ P) ⇒ TND P
raa⇒tnd raa = raa nnpnp

{- natural numbers -}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_ 

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 7 _*_ 

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n

{- Lists -}

infixr 5 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A -- \::

_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

{- Streams -}

record Stream (A : Set) : Set where
  constructor _∷_
  coinductive
  field
    head : A
    tail : Stream A

open Stream public

mapS : (A → B) → Stream A → Stream B
head (mapS f as) = f (head as)
tail (mapS f as) = mapS f (tail as)

{- conatural numbers -}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞

open ℕ∞ public

zero∞ : ℕ∞
pred∞ zero∞ = nothing

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ n) = just n

∞ : ℕ∞
pred∞ ∞ = just ∞

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m +∞ n) with pred∞ m
... | nothing = pred∞ n
... | just m' = just (m' +∞ n)

{- Vectors and Fin -}

variable i j k m n : ℕ

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

_++v_ : Vec A m → Vec A n → Vec A (m + n)
[] ++v ys = ys
(x ∷ xs) ++v ys = x ∷ (xs ++v ys)

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

_!!v_ : Vec A n → Fin n → A
(x ∷ xs) !!v zero = x
(x ∷ xs) !!v suc i = xs !!v i
