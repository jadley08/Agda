module ex-set2 where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

--exercise set 2

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

indℕ : (tgt : ℕ) → (mot : ∀ n → Set)
       → (mot zero)
       → (∀ n → mot n → mot (succ n))
       → mot tgt
indℕ zero mot base step = base
indℕ (succ tgt) mot base step = step tgt (indℕ tgt mot base step)


_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)


data 𝔹 : Set where
  true : 𝔹
  false : 𝔹



if : {X : Set} → (test : 𝔹) → (then : X) → (else : X) → X
if true then else = then
if false then else = else


if-t : (if true (succ zero) zero) ≡ (succ zero)
if-t = refl

if-f : (if false (succ zero) zero) ≡ zero
if-f = refl



_<_ : ℕ → ℕ → 𝔹
zero < zero = false
zero < succ b = true
succ a < zero = false
succ a < succ b = a < b

-- (λ a b → b < a) [RIGHT ARG]

∘ : {A B C : Set} → (f1 : A → B) → (f2 : B → C) → A → C
∘ f1 f2 a = f2 (f1 a)


plus1 : ℕ → ℕ
plus1 n = succ n



∘-p1-p1=p2-0 : (∘ plus1 plus1 zero) ≡ (succ (succ zero))
∘-p1-p1=p2-0 = refl



data List (X : Set) : Set where
  []   : List X
  _::_ : (x : X) → (xs : List X) → List X


sum-List : (l : List ℕ) → ℕ
sum-List [] = zero
sum-List (x :: l) = x + sum-List l



maybe-last : {X : Set} → List X → (default : X) → X
maybe-last [] default = default
maybe-last (x :: l) default = maybe-last l x


ml-1 : (maybe-last [] zero) ≡ zero
ml-1 = refl

ml-2 : (maybe-last ((succ zero) :: []) zero) ≡ (succ zero)
ml-2 = refl

ml-3 : (maybe-last ((succ (succ zero)) :: ((succ zero) :: [])) zero) ≡ (succ zero)
ml-3 = refl



how-many : {X : Set} → (X → 𝔹) → List X → ℕ
how-many p [] = zero
how-many p (x :: l) = if (p x) (succ (how-many p l)) (how-many p l)


hm-1 : (how-many (λ n → n < (succ (succ zero))) (zero ::
                                                      ((succ (succ (succ zero))) ::
                                                      ((succ (succ zero)) ::
                                                      ((succ (zero)) ::
                                                      [])))))
       ≡
       (succ (succ zero))
hm-1 = refl


data Vec (X : Set) : ℕ → Set where
  vecnil  : Vec X zero
  _vec::_ : ∀ {n : ℕ} (x : X) (xs : Vec X n) → Vec X (succ n)


vec-second :  {X : Set} → {k : ℕ} → Vec X (succ (succ k)) → X
vec-second (x vec:: (x₁ vec:: xs)) = x₁


vs-1 : (vec-second (zero vec::
                         ((succ zero) vec::
                         ((succ (succ zero)) vec::
                         vecnil))))
       ≡
       (succ (zero))
vs-1 = refl



vec:::: : {X : Set} → {k : ℕ} → (x : X) → Vec X k → Vec X (succ (succ k))
vec:::: x v = x vec:: (x vec:: v)


v:-1 : (vec:::: zero ((succ zero) vec:: vecnil)) ≡ (zero vec:: (zero vec:: ((succ zero) vec:: vecnil)))
v:-1 = refl


--exercise set 3
repeat : {E : Set} → E → (k : ℕ) → Vec E k
repeat e zero = vecnil
repeat e (succ k) = e vec:: repeat e k


add-to-front : {E : Set} → {k : ℕ} → (n : ℕ) → E → Vec E k → Vec E (n + k)
add-to-front zero e v = v
add-to-front (succ n) e v = e vec:: add-to-front n e v



append : {E : Set} → {n m : ℕ} → Vec E n → Vec E m → Vec E (n + m)
append vecnil vm = vm
append (x vec:: vn) vm = x vec:: append vn vm




--exercise set 4
id : {X : Set} → X → X
id x = x


sub1 : ℕ → ℕ
sub1 zero = zero
sub1 (succ n) = n


sub1' : ℕ → ℕ
sub1' x = indℕ x
              (λ _ → ℕ)
              zero
              (λ c-1 sub1-c-1 → c-1)



_-_ : ℕ → ℕ → ℕ
zero - m = zero
succ n - zero = succ n
succ n - succ m = n - m


_-'_ : ℕ → ℕ → ℕ
n -' m = indℕ m (λ _ → ℕ) n (λ c-1 n-c-1 → succ n-c-1)


max : ℕ → ℕ → ℕ
max zero m = m
max (succ n) zero = succ n
max (succ n) (succ m) = succ (max n m)



_+'_ : ℕ → ℕ → ℕ
n +' m = indℕ n (λ k → ℕ) m (λ k n+k → succ n+k)

+'-1 : (succ zero) +' zero ≡ (succ zero)
+'-1 = refl

+'-2 : zero +' (succ zero) ≡ (succ zero)
+'-2 = refl

+'-3 : (succ zero) +' (succ zero) ≡ (succ (succ zero))
+'-3 = refl



+-left-zero : ∀ (n : ℕ) → zero + n ≡ n
+-left-zero n = indℕ n (λ k → zero + k ≡ k) refl (λ k 0+k=k → cong succ 0+k=k)


+-right-zero : ∀ (n : ℕ) → n + zero ≡ n
+-right-zero n = indℕ n (λ k → k + zero ≡ k) refl (λ k k+0=k → cong succ k+0=k)

+-right-zero' : ∀ (n : ℕ) → n + zero ≡ n
+-right-zero' zero = refl
+-right-zero' (succ n) = cong succ (+-right-zero' n)


vec→list : {E : Set} → {n : ℕ} → Vec E n → List E
vec→list vecnil = []
vec→list (x vec:: v) = x :: vec→list v



snoc-vec : {E : Set} → {n : ℕ} → Vec E n → E → Vec E (succ n)
snoc-vec vecnil e = e vec:: vecnil
snoc-vec (x vec:: v) e = x vec:: snoc-vec v e



+-left-add1 : ∀ (n m : ℕ) → (succ n) + m ≡ succ (n + m)
+-left-add1 n m = indℕ n
                       (λ k → succ k + m ≡ succ (k + m))
                       refl
                       (λ k IH → cong succ IH)


+-right-add1 : ∀ (n m : ℕ) → n + (succ m) ≡ succ (n + m)
+-right-add1 n m = indℕ n
                        (λ k → k + succ m ≡ succ (k + m))
                        refl
                        (λ k IH → cong succ IH)



+-assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc x y z = indℕ x
                     (λ k → k + (y + z) ≡ (k + y) + z)
                     refl
                     (λ k IH → cong succ IH)


symm : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
symm refl = refl


+-assoc2 : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc2 x y z = symm (+-assoc x y z)


+-right-1 : ∀ (n m : ℕ) → n + succ m ≡ succ (n + m)
+-right-1 n m = indℕ n
                       (λ k → k + succ m ≡ succ (k + m))
                       refl
                       (λ k k+1+m=1+k+m → cong succ k+1+m=1+k+m)

{--
trans' : ∀ {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
trans' = {!!}
--}

+-comm : ∀ (n m : ℕ) → n + m ≡ m + n
+-comm n m = indℕ n
                  (λ k → k + m ≡ m + k)
                  (trans (+-left-zero m) (symm (+-right-zero m)))
                  (λ k k+m=m+k →
                    begin
                      succ k + m
                    ≡⟨ refl ⟩
                      succ (k + m)
                    ≡⟨ cong succ k+m=m+k ⟩
                      succ (m + k)
                    ≡⟨ symm (+-right-1 m k) ⟩
                      m + succ k
                    ∎)


+-comm' : ∀ (n m : ℕ) → n + m ≡ m + n
+-comm' zero m = symm (+-right-zero m)
+-comm' (succ n) m =
  begin
    succ n + m
  ≡⟨ refl ⟩
    succ (n + m)
  ≡⟨ cong succ (+-comm' n m) ⟩
    succ (m + n)
  ≡⟨ symm (+-right-1 m n) ⟩
    m + succ n
  ∎


max-zero-left : ∀ (n : ℕ) → (max zero n) ≡ n
max-zero-left n = refl


max-zero-right : ∀ (n : ℕ) → (max n zero) ≡ n
max-zero-right zero = refl
max-zero-right (succ n) = refl


max-idempotent : ∀ (n : ℕ) → n ≡ (max n n)
max-idempotent zero = refl
max-idempotent (succ n) = cong succ (max-idempotent n)



reverse-Vec : {E : Set} → {n : ℕ} → Vec E n → Vec E n
reverse-Vec vecnil = vecnil
reverse-Vec (x vec:: v) = snoc-vec (reverse-Vec v) x



--exercise set 5
_*_ : ℕ → ℕ → ℕ
zero * m = zero
succ n * m = n + (n * m)


twice : ℕ → ℕ
twice n = n + n


double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))


twice=double : ∀ (n : ℕ) → twice n ≡ double n
twice=double zero = refl
twice=double (succ n) =
  begin
    twice (succ n)
  ≡⟨ refl ⟩
    (succ n) + (succ n)
  ≡⟨ +-right-add1 (succ n) n ⟩
    succ ((succ n) + n)
  ≡⟨ refl ⟩
  succ (succ (n + n))
  ≡⟨ refl ⟩
  succ (succ (twice n))
  ≡⟨ cong (λ k → succ (succ k)) (twice=double n) ⟩
  succ (succ (double n))
  ≡⟨ refl ⟩
    double (succ n)
  ∎



thrice : ℕ → ℕ
thrice n = n + (n + n)


triple : ℕ → ℕ
triple zero = zero
triple (succ n) = succ (succ (succ (triple n)))



two : ℕ
two = succ (succ zero)


+kdouble=triple : ∀ (k : ℕ) → k + double k ≡ triple k
+kdouble=triple zero = refl
+kdouble=triple (succ k) =
  begin
    succ k + double (succ k)
  ≡⟨ refl ⟩
    succ (k + double (succ k))
  ≡⟨ refl ⟩
    succ (k + (succ (succ (double k))))
  ≡⟨ refl ⟩
    succ (k + (two + (double k)))
  ≡⟨ cong succ (+-assoc k two (double k)) ⟩
    succ ((k + two) + (double k))
  ≡⟨ cong (λ hole → succ (hole + double k)) (+-comm k two) ⟩
    succ ((two + k) + (double k))
  ≡⟨ refl ⟩
    succ (succ (succ (k + (double k))))
  ≡⟨ cong (λ hole → succ (succ (succ hole))) (+kdouble=triple k) ⟩
    succ (succ (succ (triple k)))
  ≡⟨ refl ⟩
    triple (succ k)
  ∎



thrice=triple : ∀ (k : ℕ) → thrice k ≡ triple k
thrice=triple zero = refl
thrice=triple (succ k) =
  begin
    thrice (succ k)
  ≡⟨ refl ⟩
    succ (k + (twice (succ k)))
  ≡⟨ cong (λ hole → succ (k + hole)) (twice=double (succ k)) ⟩
    succ (k + (double (succ k)))
  ≡⟨ refl ⟩
    (succ k) + (double (succ k))
  ≡⟨ +kdouble=triple (succ k) ⟩
    triple (succ k)
  ∎



--try writing it with replace instead of cong, and trans instead of begin
--okay : TODO aka ?




*0-l : ∀ (n : ℕ) → zero * n ≡ zero
*0-l n = refl


*0-r : ∀ (n : ℕ) → n * zero ≡ zero
*0-r zero = refl
*0-r (succ n) =
  begin
    (succ n) * zero
  ≡⟨ {!!} ⟩
    zero
  ∎


*0-r' : ∀ (n : ℕ) → n * zero ≡ zero
*0-r' n = indℕ n (λ k → k * zero ≡ zero) refl (λ k k*0=0 → {!!})


*1-l : ∀ (n : ℕ) → (succ zero) * n ≡ n
*1-l zero = refl
*1-l (succ n) =
  begin
    (succ zero) * (succ n)
  ≡⟨ {!!} ⟩
    succ n
  ∎


*1-r : ∀ (n : ℕ) → n * (succ zero) ≡ n
*1-r zero = refl
*1-r (succ n) =
  begin
    (succ n) * (succ zero)
  ≡⟨ {!!} ⟩
    (succ n)
  ∎


*succ-l : ∀ (a b : ℕ)  → (succ a) * b ≡ b + (a * b)
*succ-l zero b =
  begin
    (succ zero) * b
  ≡⟨ *1-l b ⟩
    b
  ≡⟨ symm (+-right-zero b) ⟩
    b + zero
  ≡⟨ refl ⟩
    b + (zero * b)
  ∎
*succ-l (succ a) b =
  begin
    (succ (succ a)) * b
  ≡⟨ {!!} ⟩
    b + ((succ a) * b)
  ∎


*succ-r : ∀ (a b : ℕ) → a * (succ b) ≡ a + (a * b)
*succ-r zero b = refl
*succ-r (succ a) b =
  begin
    (succ a) * (succ b)
  ≡⟨ {!!} ⟩
    (succ a) + ((succ a) * b)
  ∎


a+b+c=b+a+c : ∀ (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
a+b+c=b+a+c zero b c = refl
a+b+c=b+a+c (succ a) b c =
  begin
    (succ a) + (b + c)
  ≡⟨ refl ⟩
    succ (a + (b + c))
  ≡⟨ cong succ (+-assoc a b c) ⟩
    succ ((a + b) + c)
  ≡⟨ cong (λ hole → succ (hole + c)) (+-comm a b) ⟩
    succ ((b + a) + c)
  ≡⟨ symm (cong succ (+-assoc b a c)) ⟩
    succ (b + (a + c))
  ≡⟨ symm (+-right-add1 b (a + c)) ⟩
    b + (succ (a + c))
  ≡⟨ refl ⟩
    b + ((succ a) + c)
  ∎


rotate+ : ∀ (w x y z : ℕ) → (w + x) + (y + z) ≡ (w + y) + (x + z)
rotate+ w x y z =
  begin
    (w + x) + (y + z)
  ≡⟨ +-assoc (w + x) y z ⟩
    ((w + x) + y) + z
  ≡⟨ cong (λ hole → hole + z) (symm (+-assoc w x y)) ⟩
    (w + (x + y)) + z
  ≡⟨ cong (λ hole → (w + hole) + z) (+-comm x y) ⟩
    (w + (y + x)) + z
  ≡⟨ cong (λ hole → hole + z) (+-assoc w y x) ⟩
    ((w + y) + x) + z
  ≡⟨ symm (+-assoc (w + y) x z) ⟩
    (w + y) + (x + z)
  ∎


*-distributes : ∀ (l m n : ℕ) → l * (m + n) ≡ (l * m) + (l * n)
*-distributes zero m n = refl
*-distributes (succ l) m n =
  begin
    (succ l) * (m + n)
  ≡⟨ *succ-l l (m + n) ⟩
    (m + n) + (l * (m + n))
  ≡⟨ cong (λ hole → (m + n) + hole) (*-distributes l m n) ⟩
    (m + n) + ((l * m) + (l * n))
  ≡⟨ rotate+ m n (l * m) (l * n) ⟩
    (m + (l * m)) + (n + (l * n))
  ≡⟨ cong (λ hole → hole + (n + (l * n))) (symm (*succ-l l m)) ⟩
    ((succ l) * m) + (n + (l * n))
  ≡⟨ cong (λ hole → (succ l * m) + hole) (symm (*succ-l l n)) ⟩
    ((succ l) * m) + ((succ l) * n)
  ∎


--exercise set 6
