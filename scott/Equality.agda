module scott.Equality where

-- We take a parameter x from implicit set A.
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

-- Let us prove that _≡_ is an equivalence relation.

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
-- We know: refl {x} {y}
-- This entails the type of x is the type of y.
-- Then we know that refl {y} {x} also holds.

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
-- This is similar. Now we know: refl {x} {y}; refl {y} {z}
-- This entails x and y share a type, y and z share a type.
-- Hence x and z share a type.
-- We can deduce refl {x} {z}.

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → (f x) ≡ (f y)
cong f refl = refl
-- By refl {x} {y}, we know x and y are of the same type.
-- As f is a pure fuction, (f x) must be (f y).

cong₂ : ∀ {A B C : Set} (f : A → B → C) {x y : A} {u v : B}
    → x ≡ y → u ≡ v → (f x u) ≡ (f y v)
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → (f x) ≡ (g x)
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → (P x) → (P y)
subst P refl px = px
-- As refl {x} {y} entails x and y share a type, then px is (P y).

-- So how do we enable inline proofs?

module ≡-Reasoning {A : Set} where
  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎
  
  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

-- Example
trans' : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
-- Note: begin binds most loosely, then ≡⟨⟩, then ∎.
-- The proof is as follows.
-- 1. _∎ binds to z, giving (refl z z) : (y ≡ y)
-- 2. _≡⟨_⟩_ binds to y, y≡z, (refl y y), giving (refl y z) : (y ≡ z)
-- 3. _≡⟨_⟩_ binds to x, x≡y, (refl y z), giving (refl x z) : (x ≡ z)
-- 4. begin_ binds to (refl x z), giving (refl x z) : (x ≡ z)
-- We have derived a type in x ≡ z, so there is a proof that x ≡ z.
-- If we "simplify" this is: trans x≡y (trans y≡z refl)

-- Let's reproduce some prior proofs, given our new insight into ≡-Reasoning.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  -- We know that (+-identity m) evaluates to m + zero ≡ m.
  -- Then by transitivity, we obtain the type m + zero ≡ zero + m.
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  -- This is applying transitivity once again.
  -- This gives m + (suc n) ≡ (suc n) + m
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  -- Recall that cong yields the type suc (m + n) ≡ suc (n + m).
  -- By transitivity, this gives us that suc (m + n) ≡ suc (n) + m.
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n) + m
  ∎

-- Let's try applying this to inequality.

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

module ≤-Reasoning where
  infix  1 start_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _end

  start_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  start_ x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _end : ∀ (x : ℕ) → x ≤ x
  x end = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → (n + p) ≤ (n + q)
+-monoʳ-≤ zero p q p≤q =
  start
    p
  ≤⟨ p≤q ⟩
    q
  end
+-monoʳ-≤ (suc n) p q p≤q =
  start
    (suc n) + p
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    (suc n) + q
  end

-- Now let's rebuild rewriting for the case of parity.
-- Rewrite is a built-in feature of Agda, enabled for some notion of equality.

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n ev rewrite +-comm n m = ev

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' zero    n  rewrite +-identity n             =  refl
+-comm' (suc m) n  rewrite +-suc n m | +-comm' m n  =  refl

-- So can we avoid using rewrite? Is it syntatic sugar, just like case splits are?

even-comm' : ∀ (m n : ℕ) → even (m + n) → even (n + m)
-- We assert that m + n equals n + m with appropriate evidence.
-- If we match +-comm m n, we force a match with n + m.
even-comm' m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev

-- So fr we have used Martin Lof equality. This was defined in 1975 and asserts
-- that two objects are equal if they have the same type. An earlier definition
-- by Leibniz is that two objects are equal if no property (predicate) in your
-- theory can distingusih them. We will prove that Leibniz equality is logically
-- equivalent to Lof's equality.

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
--  This definition is a theorem parameterized by types x and y.
--  We say that (x ≐ y) if we can derive such a proof.

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px -- This line is the proof that for each P: (P x → P x)

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)
--  Using x≐y, and the fact Px, we can deduce that for P, (P y).
--  Using y≐z, and the new fact (P y), we can deduce that for P, (P z).
--  This is a proof that given ANY Px, we can ALWAYS deduce (P y).

sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    -- Q is a predicate where (Q z) says (P z) implies (P x).
    Q : A → Set
    Q z = P z → P x
    -- (P x) implies (P x), as we proved, hence (Q x).
    Qx : Q x
    Qx = refl-≐ P    -- T
    -- We know that (Q x) holds, from above.
    -- Furthermore, we know from x≐y, that (Q y) must hold.
    -- If we expand (Q y), we find that (P y) imples (P x).
    -- This is the evidence we need for y≐x, as desired.
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    -- This uses the same trick as above.
    -- We construct a predicate Q such that (Q y) is our result.
    -- We show that (Q x) holds (ideally, in some trivial way).
    -- By application of ≐ we then conclude (Q y).
    -- Consequencely, we have proven the result we had in mind.
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

-- Our definition for ≐ compares types in Set using types in Set₁.
-- In general, we should be able to compare types in Set(n) using types in Set(n+1).
-- We can do this by defining wrt. an arbitrary universe.
-- This is called: universe polymorphism.

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
--  As these names suggest, Level is isomorphic to ℕ.
--  ⊔ is the lowest upper bound of two levels, Setᵢ and Setⱼ.

data _≡'_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl' : x ≡' x

sym' : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡' y → y ≡' x
sym' refl' = refl'

_≐'_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐'_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

-- Levels are very general. Let's use composition as a final example.

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)
