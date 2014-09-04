
module Part1 where

open import Prelude

-- Exercise: Add function types, lambda and apply to the expression language.

-- types live in set
-- nat and bool are elements of a type, not the real Nat and Bool of Agda
data Type : Set where
  nat : Type
  bool : Type


-- a Ctxt is a list of Type, ie a Ctxt is like nat::bool::[]
Cxt = List Type

-- zero and suc take lots of args; these are implicit, so you can write terms like (suc zero); these are evidence for types, which look like x ∈ xs there x is an A and xs is a List A, and the whole "x ∈ xs" is a type
infix 3 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : ∀ {xs} → x ∈ x ∷ xs
  suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

-- Expr G nat is a type; the type of expressions well-formed in G and
-- which eval to a nat G is of type Cxt; Ctxt is the type of things of
-- the form nat::bool::[] etc so G is a concrete argument of this form
-- (eg nat::bool::[]); an env actually gives concrete vals for a G
data Expr (Γ : Cxt) : Type → Set where
  var   : ∀ {a} → a ∈ Γ → Expr Γ a
  lit   : (n : Nat) → Expr Γ nat
  true  : Expr Γ bool
  false : Expr Γ bool
  less  : (a b : Expr Γ nat) → Expr Γ bool
  plus  : (a b : Expr Γ nat) → Expr Γ nat
  if    : ∀ {t} (a : Expr Γ bool) (b c : Expr Γ t) → Expr Γ t

tmp5 : Cxt
tmp5 = nat ∷ []

tmp6 : nat ∈ tmp5
tmp6 = zero

tmp7 : Expr tmp5 nat
tmp7 = var tmp6

tmp8 : Expr (nat ∷ bool ∷ []) bool
tmp8 = var (suc zero)

-- Value is something that relates the constructors nat and bool to Nat and Bool
Value : Type → Set
Value nat = Nat
Value bool = Bool

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

tmp : All Value []
tmp = []

tmp2 : All Value (nat ∷ [])
tmp2 = 0 ∷ []


data Any {A : Set} (P : A → Set) : List A → Set where
  zero : ∀ {x xs} → P x → Any P (x ∷ xs)
  suc  : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

_∈′_ : {A : Set} (x : A) → List A → Set
x ∈′ xs = Any (λ y → x ≡ y) xs

-- lookup takes a proof that All P xs (which is like a list), and x :
-- xs, and gives an x for which P holds
lookup∈ : ∀ {A} {P : A → Set} {x xs} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) zero = p
lookup∈ (p ∷ ps) (suc i) = lookup∈ ps i

tmp3 : Value nat
tmp3 = lookup∈ tmp2 zero


-- Env takes a Cxt (which is eg nat::bool::[]) and produces a type
-- Value is a function from nat to Nat etc; so All Value G is a list type eg Nat::Bool::[]
Env : Cxt → Set
Env Γ = All Value Γ

tmp4 : Env (nat ∷ [])
tmp4 = 0 ∷ []

-- Value nat is Nat
eval : ∀ {Γ t} → Env Γ → Expr Γ t → Value t
eval env (var x) = lookup∈ env x
eval env (lit n) = n
eval env true = true
eval env false = false
eval env (less e e₁) = eval env e < eval env e₁
eval env (plus e e₁) = eval env e + eval env e₁
eval env (if e e₁ e₂) = if eval env e then eval env e₁ else eval env e₂

tmp9 : Bool
tmp9 = eval (0 ∷ true ∷ []) (var (suc (zero)))
