{-
  Function types
  A , B : Set -- Set = Type
  A → B : Set

  Products and sums
  A × B : Set
  A ⊎ B : Set -- disjoint union

  Don't have A ∪ B : Set! And neither A ∩ B : Set.
  These are evil operations, because they depend on elements.
-}

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_

variable
  A B C : Set

{-
  _,_ : A → B → A × B
  proj₁ (a , b) = a -- copattern matching
  proj₂ (a , b) = b
-}

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : (A → B → C) → (A × B → C)
uncurry g x = g (proj₁ x) (proj₂ x)

{-
  These two functions are inverses.
  How is this isomorphism called? Adjunction.
  Explains the relation between functions and product.
  Functions are "right adjoint" to product.
-}

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case : (A → C) → (B → C) → (A ⊎ B → C)
case f g (inj₁ a) = f a -- x C-c C-c
case f g (inj₂ b) = g b

-- uncurry case
uncase : (A ⊎ B → C) → (A → C) × (B → C)
proj₁ (uncase f) a = f (inj₁ a)
proj₂ (uncase f) b = f (inj₂ b)

{-
  These functions are inverse to each other they witness that ⊎ is a left
  adjoint (of the diagonal).
  If functions are the right adjoint of products what is the left adjoint of
  sums (⊎)?
-}

-- data is defined by constructors   _⊎_ , _×_
-- codata (record) is defined by destructors  _×_ , _→_
{-
  data _×'_ (A B : Set) : Set where
    _,_ : A → B → A ×' B
    proj₁' : A × B → A
    proj₁' (a , b) = a -- pattern matching
-}

-- What about nullary, empty product, empty sum?

record ⊤ : Set where -- the unit type, it has exactly one element tt.
  constructor tt
{-
  tt : ⊤
  tt = record {} 
-}

data ⊥ : Set where -- this is the empty type, no elements.
case⊥ : ⊥ → C
case⊥ () -- impossible pattern

-- In classical propositional logic: prop = Bool
prop = Set -- the type of evidence: propositions as type explanations
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
