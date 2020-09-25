module equality where
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl yz = yz

-- Given a proof that P x holds, P y also holds
-- ∀ P → P x → P y is of type Set₁
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ xy yz P Px = yz P (xy P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x

-- Why is Py → Px of type Set ?
-- Py returns a Set and Px returns a Set.
-- So shouldn't Py → Px be of type Set₁ → Set₁ ?
-- Q is a function from A to Set. It can replace P in the definition of _≐_
-- Qy is proof that P y → P x holds
-- Qx is true because of refl-≐
-- Qy holds because x≐y Q Qx
sym-≐ {A} {x} {y} x≐y P  = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx
