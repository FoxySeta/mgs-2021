{-
Function types

A , B : Set -- Set = Type
A → B : Set

products and sums
A × B : Set
A ⊎ B : Set -- disjoint union

Don't have A ∪ B : Set! And neither A ∩ B : Set
These are evil operations, because they depend on elements.
-}

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_
-- C-c C-d derive type

variable
  A B C : Set

{-
_,_ : A → B → A × B
proj₁ (a , b) = a -- copattern matching
proj₂ (a , b) = b
-}
-- copattern matching
-- to define an element of a record, you eed to say what are
-- its projections.

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : (A → B → C) → (A × B → C)
uncurry g x = g (proj₁ x) (proj₂ x)

-- these two functions are inverses.
-- how is this isomorphism called? adjunction
-- explains the relation between functions and product
-- functions are "right adjoint" to product.

-- \uplus
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- sum, coproduct, disjoint union

case : (A → C) → (B → C) → (A ⊎ B → C)
case f g (inj₁ a) = f a -- x C-c C-c
case f g (inj₂ b) = g b

-- uncurry case

uncase : (A ⊎ B → C) → (A → C) × (B → C)
proj₁ (uncase f) a = f (inj₁ a)
proj₂ (uncase f) b = f (inj₂ b)

-- these functions are inverse to each other
-- they witness that ⊎ is a left adjoint (of the diagonal)
-- if functions are the right adjoint of products
-- what is the left adjoint of sums (⊎)?

-- data is defined by constructors   _⊎_ , _×_
-- codata (record) is defined by destructors  _×_ , _→_
{-
data _×'_ (A B : Set) : Set where
  _,_ : A → B → A ×' B

proj₁' : A × B → A
proj₁' (a , b) = a -- pattern matching
-}
-- binary products and sums
-- nullary, empty product, empty sum?

record ⊤ : Set where
  constructor tt
{-
tt : ⊤
tt = record {}
-}
-- the unit type, it has exactly one element tt.

data ⊥ : Set where

-- this is the empty type, no elements.
case⊥ : ⊥ → C
case⊥ () -- impossible pattern

-------
{-
propositional logic, clqassical : prop = Bool
-}
prop = Set -- the type of evidence
-- in HoTT prop = hprop = types with at most inhabitant

variable
  P Q R : prop

infixl 5 _∧_
_∧_ : prop → prop → prop
P ∧ Q = P × Q

infixl 3 _∨_
_∨_ : prop → prop → prop
P ∨ Q = P ⊎ Q

infixr 2 _⇒_
_⇒_ : prop → prop → prop
P ⇒ Q = P → Q

-- propositions as types explanation

True : prop
True = ⊤

False : prop
False = ⊥

¬ : prop → prop
¬ P = P ⇒ False

infix 1 _⇔_
_⇔_ : prop → prop → prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

deMorgan : ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q
proj₁ deMorgan x = (λ p → x (inj₁ p)) , λ q → x (inj₂ q)
proj₂ deMorgan y (inj₁ p) = proj₁ y p
proj₂ deMorgan y (inj₂ q) = proj₂ y q

-- the other direction is no logical truth in intuitionistic logic
deMorgan' : (¬ P ∨ ¬ Q) ⇒ ¬ (P ∧ Q) 
deMorgan' (inj₁ x) z = x (proj₁ z)
deMorgan' (inj₂ x) z = x (proj₂ z)

{-

Exercises for TYP at MGS 2021

Tuesday

Try to prove the following propositions.
Warning: not all of them may be provable!
-}

p1 : P ⇔ P ∧ P
proj₁ p1 x = x , x
proj₂ p1 y = proj₁ y -- or proj₂ y

p2 : P ∨ ¬ P ⇒ (¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q)
proj₁ (p2 (inj₁ x)) y = {!!}
proj₂ (p2 (inj₁ x)) y = {!!}
proj₁ (p2 (inj₂ x)) y = {!!}
proj₂ (p2 (inj₂ x)) y = {!!}

p3 : ¬ (P ∧ ¬ P)
p3 z = proj₂ z (proj₁ z)

p4 : ¬ (P ⇔ ¬ P)
p4 z = proj₁ z (proj₂ z (λ x → proj₁ z x x)) (proj₂ z (λ x → proj₁ z x x))

p5 : ¬( ¬ (P ∨ ¬ P))
p5 z = z (inj₂ (λ x → z (inj₁ x)))

p6 : ¬ P ⇔ ¬ (¬( ¬ P))
p6 = (λ x x₁ → x₁ x) , (λ x x₁ → x (λ x₂ → x₂ x₁))

-- p7 : (¬ (¬ P) ⇒ P) ⇒ (P ∨ ¬ P) -- not intuitionistic

-- p8 : (P ∨ ¬ P) ⇒ ¬ (¬ P) ⇒ P -- not intuitionistic
