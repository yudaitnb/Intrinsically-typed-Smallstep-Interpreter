module EvalRec where

open import Data.Bool using (if_then_else_; true; false; Bool)
open import Data.Nat
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Binary.Core using (Rel)
open import Data.Product using (_,_; ∃)
open import Level using (0ℓ)
open import Function using ( _∘_; _$_ )

-- Booleans & Arithmetic expressions (Figure 3-1, 3.2) (p.34, p.41 en)
data Expr : Set where
  EZero : Expr
  ESucc : Expr → Expr
  -- EPred : Expr → Expr
  ETrue : Expr
  EFalse : Expr
  EIf : Expr → Expr → Expr → Expr
  EIszero : Expr → Expr
  EErr : Expr

-- Evaluation rules
data _⟶_ : Expr -> Expr -> Set where
  -- Figure 3-1 (p.34 en) 
  e-ifT      : ∀{e1 e2} -> (EIf ETrue e1 e2  ⟶ e1)
  e-ifF      : ∀{e1 e2} -> (EIf EFalse e1 e2 ⟶ e2)
  e-if       : ∀{t t' e1 e2} -> t ⟶ t' -> EIf t e1 e2 ⟶ EIf t' e1 e2
  -- Figure 3-2 (p.41 en)
  e-succ     : ∀{t t'} -> t ⟶ t' -> ESucc t ⟶ ESucc t'
  -- e-predzero : EPred EZero ⟶ EZero
  -- e-predsucc : ∀{t} -> EPred (ESucc t) ⟶ t
  -- e-pred     : ∀{t t'} -> t ⟶ t' -> EPred t ⟶ EPred t'
  e-iszero   : ∀{t t'} -> t ⟶ t' -> EIszero t ⟶ EIszero t'
  e-iszeroT  : EIszero EZero ⟶ ETrue
  e-iszeroF  : ∀{t} -> EIszero (ESucc t) ⟶ EFalse
  e-err      : ∀{t} -> t ⟶ EErr

-- A data type represents a multistep evaluation relation
-- data _⟶*_ (e : Expr) : Expr -> Set where
--   refl  : e ⟶* e
--   -- cons : ∀{e1 e2} -> (e ⟶ e1) -> (e1 ⟶* e2) -> (e ⟶* e2)
--   step  : ∀{e'} -> (e ⟶ e') -> (e ⟶* e')
--   trans : ∀{e1 e2} -> e ⟶* e1 -> e1 ⟶* e2 -> e ⟶* e2

-- A data type represents a 0-step or 1-step evaluation relation
data _⟶₀₁_ (e : Expr) : Expr -> Set where
  0step : e ⟶₀₁ e
  1step : ∀{e'} -> (e ⟶ e') -> (e ⟶₀₁ e')

-- 1-step evaluator
-- Given a value, return 0step because there is no 1-step evaluation rule to evaluate
-- Otherwise, return the pair of 1-step-reduced expression and the only applicable rule wrapped in 1step
eval01S : (e : Expr) -> ∃ λ e' -> (e ⟶₀₁ e')
-- For values
eval01S ETrue  = (_ , 0step)
eval01S EFalse = (_ , 0step)
eval01S EZero  = (_ , 0step)
-- For non-value expressions
eval01S (ESucc e) with eval01S e
... | (_  , 0step)   = (_ , 0step)
... | (e' , 1step r) = (ESucc e' , 1step (e-succ r))
eval01S (EIszero e) with eval01S e
... | (_  , 0step)   = (_ , 0step)
... | (e' , 1step r) = (EIszero e' , 1step (e-iszero r))
eval01S (EIf c t e) with eval01S c
... | (ETrue  , 0step) = (t , 1step e-ifT)
... | (EFalse , 0step) = (e , 1step e-ifF)
... | (c' ,   1step r) = (EIf c' t e , 1step (e-if r))
... | _ = (EErr , 1step e-err)
eval01S EErr = (_ , 0step)

-- Accessibility
-- let (X , _<_ ) is a ordered set
-- x ∈ X is accessible under _<_ ⟺ 
--   ∀y. y < x ⟹ y is also accessile
--   Intuitively, length of the chain xn < ... < x1 is finite
data Accessible {A : Set} (x : A) (_<_ : Rel A 0ℓ) : Set where
  accessible : (∀{y} -> y < x -> Accessible y _<_) -> Accessible x _<_

-- Well-foundedness
-- WellFounded X _<_: type X is Well-founded under _<_
--                ⟺  ∀x:X. x is accessible under _<_ 
WellFounded : (A : Set) -> Rel A 0ℓ -> Set
WellFounded A (_<_) = ∀{x : A} -> Accessible x (_<_)

{-
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
-}

-- foldAcc
recFun : ∀{X Y : Set}{_<_ : Rel X 0ℓ}
          -> WellFounded X (_<_) -- the definition of well-foundedness
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

-- Wellfoundedness of the evaluator: size of an expression
_<<_ : Rel (Expr) 0ℓ
t << t' = (size t) < (size t')

-- 許してください
postulate
  reduce-size : ∀ {e e'} -> (e ⟶ e') -> (e' << e)
  wf-<< : WellFounded (Expr) _<<_

evalMain : Expr -> Expr
evalMain = recFun wf-<< (evalMS)
  where
  evalMS : (e : Expr) -> ((e' : Expr) -> e' << e -> Expr) -> Expr
  evalMS e rec-call with (eval01S e)
  ... | (v , 0step)    = v
  ... | (e' , 1step r) = rec-call e' $ reduce-size r 
