module intrinsically where

-- TODO: evalMS, eval01Sのパターンマッチが不足

open import Data.Bool using (if_then_else_; true; false; Bool)
open import Data.Nat
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Binary.Core using (Rel)
open import Data.Product using (_,_; ∃)
open import Level using (0ℓ)
open import Function using ( _∘_; _$_ )

data Ty : Set where
  bool : Ty
  int : Ty

data Expr : Ty -> Set where
  EZero : Expr int
  ESucc : Expr int → Expr int
  -- EPred : Expr → Expr
  ETrue : Expr bool
  EFalse : Expr bool
  EIf : ∀{t} -> Expr bool → Expr t → Expr t → Expr t
  EIszero : Expr int → Expr bool
  -- EErr : Expr

data Val : Ty -> Set where
  VZero : Val int
  VSucc : Val int → Val int
  VTrue : Val bool
  VFalse : Val bool
  -- VErr : Val

-- 1step reduction relation
data _⟶_  : ∀ {T : Ty} -> Expr T -> Expr T -> Set where
  e-if     : ∀{t t' e1 e2} -> t ⟶ t' -> EIf t e1 e2 ⟶ EIf t' e1 e2
  e-ifT    : ∀{e1 e2} -> (EIf ETrue e1 e2  ⟶ e1)
  e-ifF    : ∀{e1 e2} -> (EIf EFalse e1 e2 ⟶ e2)

  e-succ   : ∀{t t'} -> (t ⟶ t') -> (ESucc t ⟶ ESucc t')

  -- e-pred   : ∀{t t'} -> t ⟶ t' -> EPred t ⟶ EPred t'
  -- e-predsucc : ∀{t} -> EPred (ESucc t) ⟶ t

  e-iszero : ∀{t t'} -> t ⟶ t' -> EIszero t ⟶ EIszero t'
  e-iszeroT : EIszero EZero ⟶ ETrue
  e-iszeroF : ∀{t} -> EIszero (ESucc t) ⟶ EFalse

data _⟶*_ {T} (e : Expr T) : Expr T -> Set where
  refl : e ⟶* e
  cons : ∀{e1 e2} -> (e ⟶ e1) -> (e1 ⟶* e2) -> (e ⟶* e2)
  -- step : ∀{e'} -> (e ⟶ e') -> (e ⟶* e')
  -- trans : ∀{e1 e2} -> e ⟶* e1 -> e1 ⟶* e2 -> e ⟶* e2

-- 0step or 1step
data _⟶₀₁_ {T} (e : Expr T) : Expr T -> Set where
  refl : e ⟶₀₁ e
  1step : ∀{e'} -> (e ⟶ e') -> (e ⟶₀₁ e')

eval01S : ∀{T} -> (e : Expr T) -> ∃ λ e' -> (e ⟶₀₁ e')
eval01S ETrue  = (_ , refl)
eval01S EFalse = (_ , refl)
eval01S EZero  = (_ , refl)

eval01S (ESucc e) with eval01S e
... | (_ , refl)         = (_ , refl)
... | (e' , (1step r))   = ((ESucc e') , (1step $ e-succ r))

eval01S (EIszero e) with eval01S e
... | (_ , refl)         = (_ , refl)
... | (e' , (1step r))   = ((EIszero e') , (1step $ e-iszero r))

eval01S (EIf c t e) with eval01S c
... | (ETrue  , refl)  = (t , 1step e-ifT)
... | (EFalse , refl)  = (e , 1step e-ifF)
... | (c' , (1step r)) = ((EIf c' t e) , (1step $ e-if r))



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

-- 実装めんどくさいので許してください
postulate
  wf-<< : ∀{T} -> WellFounded (Expr T) _<<_
  reduce-size : ∀ {e e'} -> (e ⟶ e') -> (e' << e)


evalMain : ∀{T} -> Expr T -> Expr T
evalMain = recFun wf-<< (evalMS)
  where
  evalMS : ∀{T} -> (e : Expr T) -> ((e' : Expr T) -> e' << e -> Expr T) -> Expr T
  evalMS EZero  rec-call = EZero
  evalMS ETrue  rec-call = ETrue
  evalMS EFalse rec-call = EFalse

  evalMS (ESucc e) rec-call with (eval01S e)
  ... | (_ , refl) = ESucc e
  ... | (e' , 1step r) = rec-call (ESucc e') (reduce-size $ e-succ r)


  evalMS (EIf c t e) rec-call with (eval01S c)
  ... | (ETrue  , refl) = rec-call t (reduce-size e-ifT)
  ... | (EFalse , refl) = rec-call e (reduce-size e-ifF)
  ... | (c' , 1step r)  = rec-call (EIf c' t e) (reduce-size (e-if r))


  evalMS (EIszero e) rec-call with (eval01S e)
  ... | (EZero , refl) = ETrue
  ... | (e' , 1step r) = rec-call (EIszero e') (reduce-size (e-iszero r))

