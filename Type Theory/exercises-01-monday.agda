-- exercises-01-monday.agda

open import Data.Nat

variable
  A B C : Set

-- Exercise 1

add3 : ℕ → ℕ
add3 x = x + 3

tw : (A → A) → A → A
tw f n = f (f n) -- tw = λ f n → f (f n)

-- evaluate: "tw tw add3 1"; derive the result (in a comment) step by step
{-
    tw tw add3 1 =
  = tw (tw add3) 1 =
  = (tw add3) (tw add3 1) =
  = (tw add3) (add3 (add3 1))
  = tw add3 7 =
  = add3 (add3 7) =
  = 13
-}

-- Exercise 2

-- derive lambda terms with the following types

f₀ : (A → B) → (B → C) → (A → C)
f₀ f g a = g (f a)

f₁ : (A → B) → ((A → C) → C) → ((B → C) → C)
f₁ f g h = g λ a -> h (f a)

f₂ : (A → B → C) → B → A → C
f₂ f b a = f a b

-- Exercise 3

-- derive a function tw-c which behaves the same as tw using only S, K (and I
-- which is defined using S and K below).

K : A → B → A
K = λ a b → a

S : (A → B → C) → (A → B) → A → C
S = λ f g x → f x (g x)

-- I = λ x → x
I : A → A
I {A} = S K (K {B = A})

{-
    λ f n → f (f n) =
  = λ f → λ n → f (f n) =
  = λ f → S (λ n → f) (λ n → f n) =
  = λ f → S (K f) f =
  = S (λ f → S (K f) (λ f → f) =
  = S (S (λ f → S) (λ f → (K f)) I =
  = S (S (K S) K) I =
-}

tw-c : (A → A) → A → A
tw-c = S (S (K S) K) I
