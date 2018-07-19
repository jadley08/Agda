module Nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

indℕ : (tgt : ℕ) → (mot : ∀ n → Set)
       → (mot zero)
       → (∀ n → mot n → mot (succ n))
       → mot tgt
indℕ zero mot base step = base
indℕ (succ tgt) mot base step = step tgt (indℕ tgt mot base step)


_+ℕ_ : ℕ → ℕ → ℕ
n +ℕ m = indℕ n (λ _ → ℕ) m (λ n₁ n₁-1+m → succ n₁-1+m)


{--
_+_ : ℕ → ℕ → ℕ
zero + m = m
succ n + m = succ (n + m)
--}


_addℕ_ : ℕ → ℕ → ℕ
n addℕ m = indℕ m (λ _ → ℕ) n (λ m₁ m₁-1+n → succ m₁-1+n)
