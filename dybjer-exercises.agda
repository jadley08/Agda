module dybjer-exercises where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

--1.Booleans

data 𝔹 : Set  where
  true : 𝔹
  false : 𝔹

¬ : 𝔹 → 𝔹
¬ true = false
¬ false = true

_∨_ : 𝔹 → 𝔹 → 𝔹
true ∨ b = true
false ∨ true = true
false ∨ false = false

_∧_ : 𝔹 → 𝔹 → 𝔹
true ∧ true = true
true ∧ false = false
false ∧ b = false

--1
_⇒_ : 𝔹 → 𝔹 → 𝔹
true ⇒ true = true
true ⇒ false = false
false ⇒ b = true


--2
--(a) excluded middle
em : (b : 𝔹) → b ∨ ¬ b ≡ true
em true = refl
em false = refl

--(b) de Morgan
dm : (a b : 𝔹) → ¬ (a ∧ b) ≡ (¬ a) ∨ (¬ b)
dm true true = refl
dm true false = refl
dm false true = refl
dm false false = refl




--2. natural numbers

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

zero? : ℕ → 𝔹
zero? zero = true
zero? (succ n) = false

two : ℕ
two = succ (succ zero)

three : ℕ
three = succ (succ (succ zero))

five : ℕ
five = succ (succ (succ (succ (succ zero))))

eight : ℕ
eight = succ (succ (succ (succ (succ (succ (succ (succ zero)))))))

--4
--(a)
_ℕ-_ : (a b : ℕ) → ℕ
zero ℕ- b = zero
succ a ℕ- zero = succ a
succ a ℕ- succ b = a ℕ- b

5-3=2 : (five ℕ- three) ≡ two
5-3=2 = refl

3-5=0 : (three ℕ- five) ≡ zero
3-5=0 = refl



_ℕ+_ : (a b : ℕ) → ℕ
a ℕ+ zero = a
a ℕ+ succ b = succ a ℕ+ b

5+3=8 : (five ℕ+ three) ≡ eight
5+3=8 = refl

_ℕ*_ : (a b : ℕ) → ℕ
zero ℕ* b = zero
succ a ℕ* b = b ℕ+ (a ℕ* b)

2*2*2=8 : ((two ℕ* two) ℕ* two) ≡ eight
2*2*2=8 = refl

5*0=0 : (five ℕ* zero) ≡ zero
5*0=0 = refl

0*5=0 : (zero ℕ* five) ≡ zero
0*5=0  = refl

8*1=8 : (eight ℕ* succ zero) ≡ eight
8*1=8 = refl

1*8=8 : (succ zero ℕ* eight) ≡ eight
1*8=8 = refl

--(b)
_^_ : (a b : ℕ) → ℕ
a ^ zero = succ zero
a ^ succ b = a ℕ* (a ^ b)


--(c)
whichℕ : {A : Set} → ℕ → A → (ℕ → A) → A
whichℕ zero base step = base
whichℕ (succ tgt) base step = step tgt

recℕ : {A : Set} → ℕ → A → (ℕ → A → A) → A
recℕ zero base step = base
recℕ (succ tgt) base step = step tgt (recℕ tgt base step)

_^'_ : (a b : ℕ) → ℕ
a ^' b = recℕ b (succ zero) (λ c a^'c → a ℕ* a^'c)


0^8=0 : (zero ^ eight) ≡ zero
0^8=0 = refl

1^8=1 : (succ zero ^ eight) ≡ succ zero
1^8=1 = refl

2^3=8 : (two ^ three) ≡ eight
2^3=8 = refl

0^'8=0 : (zero ^' eight) ≡ zero
0^'8=0 = refl

1^'8=1 : (succ zero ^' eight) ≡ succ zero
1^'8=1 = refl

2^'3=8 : (two ^' three) ≡ eight
2^'3=8 = refl


--5
--(a)
_==_ : ℕ → ℕ → 𝔹
zero == zero = true
zero == succ b = false
succ a == zero = false
succ a == succ b = a == b

--(b)
{-- works in pie, see dybjer-exercises.pie
==' : ℕ → (ℕ → 𝔹)
==' a = recℕ a zero? {!(λ k k==? (λ c (whichℕ c (zero? succ k) (λ c-1 (k==? c-1))))!}
--}


ack : ℕ → ℕ → ℕ
ack zero b = succ b
ack (succ a) zero = ack a (succ zero)
ack (succ a) (succ b) = ack a (ack (succ a) b)

