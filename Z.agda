module Z where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

--would rather have neg be represented as negation rather than sub1 as it is now
data ℤ : Set where
  zro : ℤ
  suc : ℤ → ℤ
  neg : ℤ → ℤ

{--
indℤ : (tgt : ℤ) → (mot : ∀ z → Set)
     → (mot zero)
     → (∀ (neg z) → mot z → mot (neg (neg z)))
     → (∀ (suc z) → mot z → mot (suc (suc z)))
     → mot tgt
indℤ zero mot base step = ?
indℤ (suc tgt) mot base step = ?
indℤ (neg tgt) mot base step = ?
--}

_+ℤ_ : ℤ → ℤ → ℤ
zro +ℤ m = m
suc n +ℤ zro = suc n
suc n +ℤ suc m = suc (n +ℤ suc m)
suc n +ℤ neg m = n +ℤ m
neg n +ℤ zro = neg n
neg n +ℤ suc m = n +ℤ m
neg n +ℤ neg m = neg (n +ℤ neg m)

three : ℤ
three = suc (suc (suc zro))

¬five : ℤ
¬five = neg (neg (neg (neg (neg zro))))

pf:3+¬5=-2 : (three +ℤ ¬five) ≡ neg (neg zro)
pf:3+¬5=-2 = refl


ℤ-add1 : (a : ℤ) → ℤ
ℤ-add1 zro = suc zro
ℤ-add1 (suc a) = suc (suc a)
ℤ-add1 (neg a) = a

ℤ-sub1 : (a : ℤ) → ℤ
ℤ-sub1 zro = neg zro
ℤ-sub1 (suc a) = a
ℤ-sub1 (neg a) = neg (neg a)

ℤ-comm : (a b : ℤ) → a +ℤ b ≡ b +ℤ a
ℤ-comm zro zro = refl
ℤ-comm zro (suc b) = refl
ℤ-comm zro (neg b) = refl
ℤ-comm (suc a) zro = refl
ℤ-comm (suc a) (suc b) =
  begin
     (suc a) +ℤ (suc b)
     ≡⟨ refl ⟩
     (suc (a +ℤ (suc b)))
     ≡⟨ {!(cong ℤ-add1 (ℤ-comm a (suc b)))!} ⟩
     (suc ((suc b) +ℤ a))
     ≡⟨ {!!} ⟩
     (suc b) +ℤ (suc a)
     ∎
ℤ-comm (suc a) (neg b) = {!!}
ℤ-comm (neg a) zro = refl
ℤ-comm (neg a) (suc b) = {!!}
ℤ-comm (neg a) (neg b) = {!!}
