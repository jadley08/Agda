-- Hello Agda Enthusiasts!

-- Let's play with Agda.

-- Firstly, since we're editing demo1A.agda, let's name our module correctly:

module demo1A where -- Load the file with C-c C-l - Like that!

-- Syntax is highlighted by Emacs

-- First thing's first - Let's define a simple data-type - Bools

data Bool : Set where
  true : Bool
  false : Bool

-- Notice:
 -- Definitions follow closely Haskell's GADT style data-type definitions
 -- 'Set' type for Bool data-type... Types have types? Yep.

-- Okay let's define a function that operates on this data-type - 'not'

not : Bool → Bool -- '→' is input with '\to'
not true = false
not false = true
            -- '?' represented a 'hole' this is identified by Agda for further play
            -- Jump to holes with C-c C-f..

-- This all seems simple enough, but let's define a nicer operator for this purpose

!_ : Bool → Bool
! true  = false -- C-c C-c activates case-analysis. If you already have a variable
! false = true  -- inside the hole then it uses that, else prompts for one

-- As you can see, you can use non-ascii operators.
-- '_' underscores denote place-holders for parameters in the type-signature

-- Let's define 'if'!

if_then_else_ : {A : Set} → Bool → A → A → A -- {_} defines an implicit param
if true then x else y = x
if false then x else y = y -- Case split -- Looks good!

-- That would be okay in haskell, but...
-- Agda doesn't know what 'A' is

-- Note how we have three underscores in 'if'. You can have as many as you want!
-- Syntax suddenly becomes largely user-defined

-- Now for an inductive definition - Natural Numbers

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- Note that 'suc' constructor is defined as taking a parameter in its type

-- What can we do with this? How about addition?

add : Nat → Nat → Nat
add zero y = y
add (suc y) y' = suc (add y  y') -- That's better, but I liked the look of '+'

_+_ : Nat → Nat → Nat
zero + b = b
suc y + b = suc (y + b) -- Sometimes Agda can solve for us, other times... Nope.

-- Let's try out our new addition:

low  = suc zero          -- 1?
high = low + (low + low) -- 3?

-- You can evaluate an expression with C-c C-n -- The answer is on the right ->

-- Looks okay to me!

-- Now, let's define something a bit more interesting. A List!

data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

-- Note:
 -- '(A : Set)' denotes a type parameter to the List data-type
 -- Constructors can reference this type parameter

-- Let's define some list operations: length, map, concat

length : {A : Set} → List A → Nat
length Nil = zero -- yep!
length (Cons y y') = suc (length y') -- Yep! -- Let's test it -- Looks okay!

map : {A B : Set} → (A → B) → List A → List B
map f Nil = Nil
map f (Cons y y') = Cons (f y) (map f y') -- Looks Good!

-- Note that we can group multiple type params into the same {_} block

concat : {A : Set} → List A → List A → List A
concat Nil m = m
concat (Cons y y') m = Cons y (concat y' m) -- Done! Too easy!

-- How about something a bit more unique to Agda - Check this out:
-- Vectors!

data Vector (A : Set) : Nat → Set where
  ε : Vector A zero
  _▸_ : {n : Nat} → A → Vector A n → Vector A (suc n)

-- Note:
 -- There is a type parameter to the Vector data-type, but also...
 -- A value parameter!
 -- This value parameter can then be extracted by the data constructors via
 -- Implicit parameters

-- Let's redefine those list functions for vectors:

vLength : {A : Set} → {n : Nat} → Vector A n → Nat
vLength {_} {n} v = n -- What's that all about? Doesn't Load... But...
                      -- Now it does!

-- Data-type value parameters (indexes) can be extracted by functions that operate
-- on those data-types.

vMap : {A B : Set} → {n : Nat} → (A → B) → Vector A n → Vector B n
vMap f ε = ε
vMap f (y ▸ y') = f y ▸ vMap f y' -- Wow!

-- It was a bit unexpected that that could be solved for us, but due to the
-- unambiguous nature of our vector definition it turns out that it can!
-- However, the cons operator would be a bit nicer if it was infix
-- Let's fix that.

-- Just as before, underscores denote placholders. In data-types too!

-- Now, vConcat

vConcat : {A : Set} → {n m : Nat} → Vector A n → Vector A m → Vector A (n + m)
vConcat ε w = w
vConcat (y ▸ y') w = y ▸ vConcat y' w -- And we're done!

-- Note: We are using user-defined datatypes, _and functions_ inside a type signature!

-- I hope you have enjoyed this demo. Hopefully there werent' too many typos (:-)!
