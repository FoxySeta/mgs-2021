{-

Exercises for TYP at MGS 2021
Monday - solutions

type C-c C-l
to load the file

undo = C-_
-}

open import Data.Nat

variable
  A B C : Set

{- 1. -}

add3 : ℕ → ℕ
add3 x = x + 3

tw : (A → A) → A → A
tw f n = f (f n)
-- tw = λ f n → f (f n)

-- evaluate
-- tw tw add3 1
-- C-c C-n -- to evaluate a term

-- derive the result (in a comment) step by step
-- why
{-
tw tw add3 1 
= tw (tw add3) 1
= (tw add3) (tw add3 1)
= (tw add3) (add3 (add3 1))
= tw add3 7
= add3 (add3 7)
= 13
-}

{- 2. -}

-- derive lambda terms with the following types

f₀ : (A → B) → (B → C) → (A → C)
f₀ = λ x x₁ x₂ → x₁ (x x₂)
--f₀ = λ f g a → g (f a) -- shed
--f₀ f g a = g (f a)
-- f\_0 = f₀

-- C-c C-, shows goal and all the assumptions.
-- C-c C-SPC
-- C-C C-r (refine) use the function 

f₁ : (A → B) → ((A → C) → C) → ((B → C) → C)
f₁ = λ f g h → g λ a -> h (f a)

f₂ : (A → B → C) → B → A → C
f₂ = λ f b a → f a b


{- 3. -}

-- Advanced (see lecture notes 2.4)

{-
Derive a function tw-c which behaves the same as tw 
using only S, K (and I which is defined using S and K below).
-}

K : A → B → A
K = λ a b → a

S : (A → B → C) → (A → B) → A → C
S = λ f g x → f x (g x)

-- I = λ x → x
I : A → A
I {A} = S K (K {B = A})

{-
x doesn't appear in M
λ x → M = K M

λ x → x = I 

x doesn't appear in M
λ x → M x = M

λ x → M N = S (λ x → M) (λ x → N)
-}

-- tw = λ f → λ n → f (f n)
{-
λ f n → f (f n)
= λ f → λ n → f (f n)
= λ f → S (λ n → f) (λ n → f n)
= λ f → S (K f) f
= S (λ f → S (K f) (λ f → f)
= S (S (λ f → S) (λ f → (K f)) I
= S (S (K S) K) I
-}

tw-c : (A → A) → A → A
tw-c = S (S (K S) K) I


