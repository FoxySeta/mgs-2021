-- exercises-03-wednesday.agda

open import mylib

{-
  Part 1 : Recursion via patterns
  Define the following functions using pattern matching and structural
  recursion on the natural numbers.
-}

-- Define a function even that determines wether its input is even.
even :  ℕ → Bool
{-
  even zero = true
  even (suc n) = ! even n
-}
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

-- Define a function sum that sums the numbers from 0 until n-1
sum : ℕ → ℕ
sum 0 = 0
sum (suc n) =  n + sum n

-- Define a function max that calculates the maximum of 2 numbers
max : ℕ → ℕ → ℕ
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)

-- Define a function fib which calculates the nth item of the
-- Fibonacci sequence: 1,1,2,3,5,8,13
-- (each number is the sum of the two previous ones).
fib : ℕ → ℕ
fib zero = 1
fib (suc zero) = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- Define a function eq that determines wether two numbers are equal.
eq : ℕ → ℕ → Bool
eq zero zero = true
eq zero (suc m) = false
eq (suc n) zero = false
eq (suc n) (suc m) = eq n m

-- Define a function rem such that rem m n returns the remainder
-- when dividing m by suc n (this way we avoid division by 0).
rem : ℕ → ℕ → ℕ
rem zero n = zero
rem (suc m) n = if eq (rem m n) n then 0 else suc (rem m n)

-- Define a function div such that div m n returns the result
-- of dividing m by suc n (ignoring the remainder)
div : ℕ → ℕ → ℕ
div zero n = zero
div (suc m) n = if eq (rem m n) n then suc (div m n) else div m n

{-
  Part 2 : Iterator and recursor 
  Define all the functions of part 1 but this time only use the 
  iterator Itℕ. That is NO PATTERNMATCHING (not even in lambdas) and 
  NO RECURSION. 

  Naming convention if the function in part 1 is called f then call it 
  f-i if you only use the iterator.

  Test the functions with at least the same test cases.

  Hint: you may want to derive the recursor first (from the iterator):
  Rℕ : M → (ℕ → M → M) → ℕ → M
  where the method can access the current number. Using pattern matching 
  the recursor can be defined as follows: 
  Rℕ z s zero = z
  Rℕ z s (suc n) = s n (Rℕ z s n)
-}

Itℕ : M → (M → M) → ℕ → M
Itℕ z s zero = z
Itℕ z s (suc n) = s (Itℕ z s n)

even-i :  ℕ → Bool
even-i = Itℕ true (λ even-n → ! even-n)

{-
sum : ℕ → ℕ
sum 0 = 0
sum (suc n) =  n + sum n
-}
sum-i-aux : ℕ → ℕ × ℕ -- sum-i-aux n = (n , sum n)
sum-i-aux = Itℕ (0 , 0)
  λ n-sum-n → (suc (proj₁ n-sum-n)) , ((proj₁ n-sum-n) + (proj₂ n-sum-n))

sum-i : ℕ → ℕ
sum-i n = proj₂ (sum-i-aux n)

{-
fib : ℕ → ℕ
fib zero = 1
fib (suc zero) = 1
fib (suc (suc n)) = fib n + fib (suc n)

fib-i-aux : ℕ → ℕ × ℕ  = fib-i-aux n = fib n , fib (suc n)
-}
