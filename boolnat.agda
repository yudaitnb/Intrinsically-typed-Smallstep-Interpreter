module boolnat where

open import Data.Bool.Base
open import Data.Nat

-- Booleans & Arithmetic expressions (Figure 3-1, 3.2) (p.34, p.41 en)
data Expr : Set where
  EZero : Expr
  ESucc : Expr → Expr
  EPred : Expr → Expr
  ETrue : Expr
  EFalse : Expr
  EIf : Expr → Expr → Expr → Expr
  EIszero : Expr → Expr
  EErr : Expr

-- Values
data Val : Set where
  VZero : Val
  VSucc : Val → Val 
  VTrue : Val
  VFalse : Val
  VErr : Val

isnv : Val → Bool
isnv VZero     = true
isnv (VSucc v) = isnv v
isnv _         = false

-- Bigstep semantics (p.43 en)
evalBS : Expr → Val
evalBS EZero  = VZero  -- B-Value
evalBS ETrue  = VTrue  -- B-Value
evalBS EFalse = VFalse -- B-Value
evalBS (ESucc e) = let v = evalBS e in
                   if isnv v then VSucc v -- B-Succ
                              else VErr
evalBS (EPred e) with evalBS e
... | VZero   = VZero            -- B-PredZero
... | VSucc v = if isnv v then v -- B-PredSucc
                           else VErr
... | _       = VErr                 
evalBS (EIszero e) with evalBS e
... | VZero   = VTrue                 -- B-IszeroZero
... | VSucc v = if isnv v then VFalse -- B-IszeroSucc
                          else VErr
... | _       = VErr
evalBS (EIf cond th el) with evalBS cond
... | VTrue  = evalBS th -- B-IfTrue
... | VFalse = evalBS el -- B-IfFalse
... | _      = VErr
evalBS _ = VErr

isnv' : Expr → Bool
isnv' EZero     = true
isnv' (ESucc e) = isnv' e
isnv' _         = false

isv' : Expr → Bool
isv' ETrue     = true
isv' EFalse    = true
isv' EZero     = true
isv' (ESucc e) = isnv' e
isv' _         = false

-- Smallstep semantics (Figure 3-1, 3.2) (p.34, p.41 en)
eval01S : Expr → Expr
eval01S EZero  = EZero   -- value
eval01S ETrue  = ETrue   -- value
eval01S EFalse = EFalse  -- value
eval01S (ESucc e) = ESucc (eval01S e) -- E-Succ
eval01S (EPred EZero)     = EZero                      -- E-PredZero
eval01S (EPred (ESucc t)) = if isnv' t then eval01S t   -- E-PredSucc
                                      else EErr
eval01S (EPred e)         = EPred (eval01S e)           -- E-Pred
eval01S (EIszero EZero) = ETrue                      -- E-IszeroZero
eval01S (EIszero (ESucc e)) = if isnv' e then EFalse -- E-IszeroSucc
                                        else EErr
eval01S (EIf cond th el) with cond
... | ETrue   = eval01S th                         -- E-IfTrue
... | EFalse  = eval01S el                         -- E-IfFalse
... | EZero   = EErr
... | ESucc _ = EErr
... | EPred _ = EErr
... | _       = EIf (eval01S cond) th el -- E-IfIf
eval01S _ = EErr

evalMS : Expr → Expr
{-# TERMINATING #-}
evalMS e = let v = eval01S e in
           if isv' v then v
                     else evalMS v