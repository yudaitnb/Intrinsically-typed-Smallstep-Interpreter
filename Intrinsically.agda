module Common.Test2 where

open import Data.Bool using (if_then_else_; true; false; Bool)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Base using (_<_; s≤s)
open import Data.Nat.Properties using (≤-trans; n<1+n; ≤-refl; ≤-step)
open import Relation.Binary.Core using (Rel)
open import Data.Product using (_,_; ∃)
open import Level using (0ℓ)
open import Function using ( _∘_; _$_ )
open import Data.Sum
  renaming (inj₁ to inl; inj₂ to inr)
  using (_⊎_)

data Ty : Set where
  bool : Ty
  int : Ty

data Val : Ty -> Set where
  VZero : Val int
  VSucc : Val int → Val int
  VTrue : Val bool
  VFalse : Val bool

data Expr : Ty -> Set where
  EZero : Expr int
  ESucc : Expr int → Expr int
  -- EPred : Expr → Expr
  ETrue : Expr bool
  EFalse : Expr bool
  EIf : ∀{t} -> Expr bool → Expr t → Expr t → Expr t
  EIszero : Expr int → Expr bool
  -- EErr : Expr

-- 値と式の同型
data _==_ : ∀{T} -> Val T -> Expr T -> Set where
  zero  : VZero  == EZero
  succ  : ∀{v e} -> v == e -> (VSucc v) == (ESucc e)
  true  : VTrue  == ETrue
  false : VFalse == EFalse

-- 1step reduction relation
data _⟶_  : ∀{T} -> Expr T -> Expr T -> Set where

  e-if     : ∀{T}{t t'}{e1 e2 : Expr T}
              -> t ⟶ t' -> EIf t e1 e2 ⟶ EIf t' e1 e2

  e-ifT    : ∀{T}{e1 e2 : Expr T} -> (EIf ETrue  e1 e2 ⟶ e1)
  e-ifF    : ∀{T}{e1 e2 : Expr T} -> (EIf EFalse e1 e2 ⟶ e2)

  e-succ   : ∀{t t'} -> (t ⟶ t') -> (ESucc t ⟶ ESucc t')

  -- e-pred   : ∀{t t'} -> t ⟶ t' -> EPred t ⟶ EPred t'
  -- e-predsucc : ∀{t} -> EPred (ESucc t) ⟶ t

  e-iszero : ∀{t t'} -> t ⟶ t' -> EIszero t ⟶ EIszero t'
  e-iszeroT : EIszero EZero ⟶ ETrue
  e-iszeroF : ∀{t} -> EIszero (ESucc t) ⟶ EFalse

-- data _⟶*_ {T} (e : Expr T) : Expr T -> Set where
--   refl : e ⟶* e
--   cons : ∀{e1 e2} -> (e ⟶ e1) -> (e1 ⟶* e2) -> (e ⟶* e2)
--   step : ∀{e'} -> (e ⟶ e') -> (e ⟶* e')
--   trans : ∀{e1 e2} -> e ⟶* e1 -> e1 ⟶* e2 -> e ⟶* e2

-- progress & preservation
typesafe-eval : ∀ {T} -> (e : Expr T) -> (∃ λ (v : Val T) -> (v == e)) ⊎ (∃ λ (e' : Expr T) -> (e ⟶ e'))
typesafe-eval ETrue  = inl (_ , true)
typesafe-eval EFalse = inl (_ , false)
typesafe-eval EZero  = inl (_ , zero)

typesafe-eval (ESucc e) with (typesafe-eval e)
... | inl (v  , r) = inl (VSucc v  , succ r)
... | inr (e' , r) = inr (ESucc e' , e-succ r)

typesafe-eval (EIszero e) with (typesafe-eval e)
... | inl (_ , zero)   = inr (ETrue  , e-iszeroT)
... | inl (_ , succ _) = inr (EFalse , e-iszeroF)
... | inr (e' , r)    = inr ((EIszero e') , (e-iszero r))


-- typesafe-eval (EIf c t e) with (typesafe-eval c)
-- ... | inl VTrue    = inr (t , e-ifT)  -- (c = ETrue)を教える必要がある
-- ... | inl VFalse   = inr (e , e-ifF)
-- ... | inr (c' , r) = inr ((EIf c' t e) , (e-if r))

typesafe-eval (EIf c t e) with (typesafe-eval c)
... | inl (_ , true)   = inr (t , e-ifT)
... | inl (_ , false)  = inr (e , e-ifF)
... | inr (c' , r)     = inr ((EIf c' t e) , (e-if r))


-- Accessibility
-- let (X , _<_ ) is a ordered set
-- x ∈ X is accessible under _<_ ⟺ 
--   ∀y. y < x ⟹ y is also accessile
--   Intuitively, length of the chain xn < ... < x1 is finite
data Accessible {A : Set} (x : A) (_<_ : Rel A 0ℓ) : Set where
  accessible : (∀{y} -> y < x -> Accessible y _<_) -> Accessible x _<_


-- Well-foundedness
-- X is Well-founded under _<_ ⟺ 
--   ∀x. x is accessible under _<_ 
WellFounded : (A : Set) -> Rel A 0ℓ -> Set
WellFounded A (_<_) = ∀{x : A} -> Accessible x (_<_)

-- Natの_<_のwell-foundedness
-- gotoの名前が最悪
wf-< : WellFounded ℕ (_<_)
wf-< {x} = accessible (gofrom x)
  where
  gofrom : (x : ℕ) -> ∀{y} -> y < x -> Accessible y _<_
  -- gofrom zero {m} ()  -- means ⟂
  gofrom (suc n) {zero} _ = accessible (λ ()) -- accessible $ \() -> ⟂ because zero is minimam
  gofrom (suc n) {suc m} (s≤s m+1≤n) = accessible $ λ {y} y<m+1 -> gofrom n (≤-trans y<m+1 m+1≤n)


recFun : ∀{X Y : Set}{_<_ : Rel X 0ℓ}
          -> WellFounded X (_<_)
          -> ((x : X) -> ((x' : X) -> x' < x -> Y) -> Y) -- 停止させたい関数本体？ 第二引数は再起呼び出しのガイド
          -> (X -> Y)
recFun {X}{Y}{_<_} wf f x = go (wf {x})
  where
  go : ∀{x : X} -> Accessible x _<_ -> Y
  go {x} (accessible p) = f x (λ x' x'<x -> go (p x'<x))


size : ∀{T} -> Expr T -> ℕ
size (ESucc e)   = 1 + (size e)
size (EIszero e) = 1 + (size e)
size (EIf c t e) = 1 + (size c) + (size t) + (size e)
size _ = 1


_<<_ : ∀{T} -> Rel (Expr T) 0ℓ
t << t' = (size t) < (size t')



-- 真心こめて実装中
postulate
  reduce-size : ∀ {T}{e e' : Expr T} -> (e ⟶ e') -> (e' << e)
  wf-<< : ∀{T} -> WellFounded (Expr T) _<<_


evalMain : ∀{T} -> Expr T -> Val T
evalMain = recFun wf-<< (evalMS)
  where
  evalMS : ∀{T} -> (e : Expr T) -> ((e' : Expr T) -> e' << e -> Val T) -> Val T
  evalMS e rec-call with (typesafe-eval e)
  ... | inl (v , _)  = v
  ... | inr (e' , r) = rec-call e' $ reduce-size r 

