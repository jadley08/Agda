module exerciseset2 where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

indℕ : (tgt : ℕ) → (mot : ∀ n → Set)
       → (mot zero)
       → (∀ n → mot n → mot (succ n))
       → mot tgt
indℕ zero mot base step = base
indℕ (succ tgt) mot base step = step tgt (indℕ tgt mot base step)


_add_ : ℕ → ℕ → ℕ
n add m = indℕ n (λ _ → ℕ) m (λ n₁ n₁-1+m → succ n₁-1+m)


{--
_+_ : ℕ → ℕ → ℕ
zero + m = m
succ n + m = succ (n + m)
--}


_plus_ : ℕ → ℕ → ℕ
n plus m = indℕ m (λ _ → ℕ) n (λ m₁ m₁+n → succ m₁+n)

{--
data Bool : Set where
  true : Bool
  false : Bool


¬_ : Bool → Bool
¬ true = false
¬ false = true

if_then_else : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y
--}

--true == 1
--false == 0
if_then_else_ : {X : Set} → ℕ → X → X → X
if_then_else_ {X} n x₁ x₂ = indℕ n (λ _ → X) x₁ (λ _ _ → x₂)


data _≡_ {E : Set} : E → E → Set where
  refl : (e : E) → e ≡ e

symm : ∀ {E} {e₁ e₂ : E} → e₁ ≡ e₂ → e₂ ≡ e₁
symm (refl e) = refl e

trans : ∀ {E} {e₁ e₂ e₃ : E} → e₁ ≡ e₂ → e₂ ≡ e₃ → e₁ ≡ e₃
trans (refl e) (refl .e) = refl e

cong : ∀ {X Y} {x₁ x₂ : X} → x₁ ≡ x₂ → (f : X → Y) → f x₁ ≡ f x₂
cong (refl e) f = refl (f e)


record 3-Tuple (A : Set) (B : Set) (C : Set) : Set where
  constructor ⟨_,_,_⟩
  field
    fst : A
    snd : B
    trd : C



record _×_ (A : Set) (B : Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B


record IsMonoid (E : Set) (_∙_ : E → E → E) (e : E) : Set where
  field
    ∙-id : ∀ {α : E} → (((e ∙ α) ≡ α) × ((α ∙ e) ≡ α))
    ∙-assoc : ∀ {α₁ α₂ α₃} → (α₁ ∙ (α₂ ∙ α₃)) ≡ ((α₁ ∙ α₂) ∙ α₃)


data ℤ : Set where
  zro : ℤ
  suc : ℤ → ℤ
  neg : ℤ → ℤ


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
pf:3+¬5=-2 = refl (neg (neg zro))


postulate
  neg/zro : neg zro ≡ zro
  neg/neg : (z : ℤ) → neg (neg z) ≡ z



ℤ-isMonoid : IsMonoid ℤ _+ℤ_ zro
ℤ-isMonoid = record { ∙-id = ⟨ {!!} , {!!} ⟩ ; ∙-assoc = {!!} }






{--
indℤ : (z : ℤ)
       → (P 
--}

