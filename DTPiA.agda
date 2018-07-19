module DTPiA where




data Bool : Set where
  true  : Bool
  false : Bool


¬ : Bool → Bool
¬ true = false
¬ false = true


data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ


_+_ : ℕ → ℕ → ℕ
zero   + m = m
succ n + m = succ (n + m)



_*_ : ℕ → ℕ → ℕ
zero   * m = zero
succ n * m = m + (n * m)


_or_ : Bool → Bool → Bool
true  or x = x
false or _ = false


if_then_else : {X : Set} → Bool → X → X → X
if true  then x else y = x
if false then x else y = y


data List (X : Set) : Set where
  [] : List X
  _::_ : X → List X → List X


zeros : List ℕ
zeros = zero :: (zero :: (zero :: []))

ones : List ℕ
ones = (succ zero) :: ((succ zero) :: ((succ zero) :: []))



identity : (A : Set) → A → A
identity A x = x


zero' : ℕ
zero' = identity ℕ zero


apply : (A : Set)(B : A → Set) → ((x : A) → B x) → (a : A) → B a
apply A B f a = f a



identity₂ : (A : Set) → A → A
identity₂ = \A x → x

identity₃ : (A : Set) → A → A
identity₃ = \(A : Set)(x : A) → x

identity₄ : (A : Set) → A → A
identity₄ = \(A : Set) x → x


--{} for implicit arguments
id : {A : Set} → A → A
id x = x


zero'' : ℕ
zero'' = id zero


silly : {A : Set}{x : A} → A
silly {_}{x} = x

zero''' : ℕ
zero''' = silly {x = zero} --provide an implicit argument explicitly (equivalent to {zero})



one : ℕ
one = identity _ (succ zero) --omit an explicit term


_∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set} (f : {x : A}(y : B x) → C x y)(g : (x : A) → B x) (x : A) → C x (g x)
(f ∘ g) x = f (g x)


--plus-two = _+_ ∘ succ --why does this type check?
plus-two = succ ∘ succ



map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs


_++_ : {A : Set} → List A → List A → List A
[] ++ ys        = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

zeros&ones : List ℕ
zeros&ones = zeros ++ ones
