module EvalRec where


open import Data.Bool using (if_then_else_; true; false; Bool)
open import Data.Nat
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Binary.Core using (Rel)
open import Data.Product using (_,_; ∃)
open import Level using (0ℓ)
open import Function using ( _∘_; _$_ )

data Expr : Set where
  EZero : Expr
  ESucc : Expr → Expr
  -- EPred : Expr → Expr
  ETrue : Expr
  EFalse : Expr
  EIf : Expr → Expr → Expr → Expr
  EIszero : Expr → Expr
  EErr : Expr

-- 1step reduction relation
data _⟶_ : Expr -> Expr -> Set where
  e-if     : ∀{t t' e1 e2} -> t ⟶ t' -> EIf t e1 e2 ⟶ EIf t' e1 e2
  e-ifT    : ∀{e1 e2} -> (EIf ETrue e1 e2  ⟶ e1)
  e-ifF    : ∀{e1 e2} -> (EIf EFalse e1 e2 ⟶ e2)

  e-succ   : ∀{t t'} -> t ⟶ t' -> ESucc t ⟶ ESucc t'

  -- e-pred   : ∀{t t'} -> t ⟶ t' -> EPred t ⟶ EPred t'
  -- e-predsucc : ∀{t} -> EPred (ESucc t) ⟶ t

  e-iszero : ∀{t t'} -> t ⟶ t' -> EIszero t ⟶ EIszero t'
  e-iszeroT : EIszero EZero ⟶ ETrue
  e-iszeroF : ∀{t} -> EIszero (ESucc t) ⟶ EFalse

  e-err : ∀{t} -> t ⟶ EErr

data _⟶*_ (e : Expr) : Expr -> Set where
  refl : e ⟶* e
  -- cons : ∀{e1 e2} -> (e ⟶ e1) -> (e1 ⟶* e2) -> (e ⟶* e2)
  step : ∀{e'} -> (e ⟶ e') -> (e ⟶* e')
  trans : ∀{e1 e2} -> e ⟶* e1 -> e1 ⟶* e2 -> e ⟶* e2

-- 0step or 1step
data _⟶₀₁_ (e : Expr) : Expr -> Set where
  refl : e ⟶₀₁ e
  1step : ∀{e'} -> (e ⟶ e') -> (e ⟶₀₁ e')

eval01S : (e : Expr) -> ∃ λ e' -> (e ⟶₀₁ e')
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
... | _ = (EErr , 1step e-err)

eval01S EErr = (_ , refl)

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

-- Data.Natより抜粋
-- data _≤_ : Rel ℕ 0ℓ where
--   z≤n : ∀ {n}                 → zero  ≤ n
--   s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

-- _<_ : Rel ℕ 0ℓ
-- m < n = suc m ≤ n

-- Natの_<_のwell-foundedness
-- gotoの名前が最悪
wf-< : WellFounded ℕ (_<_)
wf-< {x} = accessible (gofrom x)
  where
  gofrom : (x : ℕ) -> ∀{y} -> y < x -> Accessible y _<_
  -- goto zero {m} ()  -- means ⟂
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


size : Expr -> ℕ
size (ESucc e)   = 1 + (size e)
size (EIszero e) = 1 + (size e)
size (EIf c t e) = 1 + (size c) + (size t) + (size e)
size _ = 1


_<<_ : Rel (Expr) 0ℓ
t << t' = (size t) < (size t')

-- 許してください
postulate
  wf-<< : WellFounded (Expr) _<<_
  reduce-size : ∀ {e e'} -> (e ⟶ e') -> (e' << e)


evalMain : Expr -> Expr
evalMain = recFun wf-<< (evalMS)
  where
  evalMS : (e : Expr) -> ((e' : Expr) -> e' << e -> Expr) -> Expr
  evalMS EZero  _ = EZero
  evalMS ETrue  _ = ETrue
  evalMS EFalse _ = EFalse
  evalMS EErr   _ = EErr

  evalMS (ESucc e) rec-call with (eval01S e)
  ... | (_ , refl) = ESucc e
  ... | (e' , 1step r) = rec-call (ESucc e') (reduce-size $ e-succ r)


  evalMS (EIf c t e) rec-call with (eval01S c)
  ... | (ETrue  , refl) = rec-call t (reduce-size {EIf c t e} e-ifT)
  ... | (EFalse , refl) = rec-call e (reduce-size {EIf c t e} e-ifF)
  ... | (c' , 1step r)  = rec-call (EIf c' t e) (reduce-size {EIf c t e} (e-if r))
  ... | _ = EErr

  evalMS (EIszero e) rec-call with (eval01S e)
  ... | (EZero , refl) = ETrue
  ... | (e' , 1step r) = rec-call (EIszero e') (reduce-size (e-iszero r))
  ... | _ = EErr

