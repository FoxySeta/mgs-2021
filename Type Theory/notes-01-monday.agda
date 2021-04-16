-- notes-01-monday.agda

open import Data.Nat
open import Data.Bool

f : ℕ → ℕ
f x = x + 2

{-
    f 3 =
  = (x + 2)[x:=3] =
  = 3 + 2 =
  = 5
-}

n : ℕ
n = 3

f' : ℕ → ℕ
f' = λ x → x + 2 -- nameless function

{-
    f' 3 =
  = (λ x → x + 2) 3 =
  = (x + 2)[x := 3] = -- β-reduction
  = 3 + 2 =
  = 5
-}

g : ℕ → ℕ → ℕ -- currying
g = λ x → (λ y → x + y)

k : (ℕ → ℕ) → ℕ
k h = h 2 + h 3

{-
    k f =
  = f 2 + f 3 = 
  = (2 + 2) + (3 + 2) =
  = 4 + 5 =
  = 9
-}

variable
  A B C : Set -- polymorphic

id : A → A
id x = x

_∘_ : (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

K : A → B → A -- combinator
K x y = x

S : (A → B → C) → (A → B) → A → C
S f g x = f x (g x)

-- in combinatory logic, every pure λ-term can be translated into S,K
-- λ x → f x = f -- η-equality
