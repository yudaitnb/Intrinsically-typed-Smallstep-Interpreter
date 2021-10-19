module boolnat where

open import Data.Bool.Base
open import Data.Nat

-- data Ty : Set where
--   Bool : Ty
--   Nat : Ty

data Expr : Set where
  EZero : Expr
  ESucc : Expr → Expr
  EPred : Expr → Expr
  ETrue : Expr
  EFalse : Expr
  EIf : Expr → Expr → Expr → Expr
  EIszero : Expr → Expr
  EErr : Expr

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

-- bigstep semantics (p.32)
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
... | VZero   = VTrue                  -- B-IszeroZero
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

-- smallstep semantics (p.25 and p.30)
-- evalSS : Expr → Expr
-- {-# TERMINATING #-}
-- evalSS EZero  = EZero   -- value
-- evalSS ETrue  = ETrue   -- value
-- evalSS EFalse = EFalse  -- value
-- evalSS (ESucc e) = ESucc (evalSS e) -- E-Succ
-- evalSS (EPred e) with e
-- ... | EZero   = EZero                      -- E-PredZero
-- ... | ESucc t = if isnv' t then evalSS t   -- E-PredSucc
--                            else EErr
-- ... | _       = evalSS (EPred (evalSS e)) -- E-Pred
-- evalSS (EIszero EZero) = ETrue                      -- E-IszeroZero
-- evalSS (EIszero (ESucc e)) = if isnv' e then EFalse -- E-IszeroSucc
--                                         else EErr
-- evalSS (EIf cond th el) with cond
-- ... | ETrue   = evalSS th                         -- E-IfTrue
-- ... | EFalse  = evalSS el                         -- E-IfFalse
-- ... | EZero   = EErr
-- ... | ESucc _ = EErr
-- ... | EPred _ = EErr
-- ... | _       = evalSS (EIf (evalSS cond) th el) -- E-IfIf
-- evalSS _ = EErr

evalOS : Expr → Expr
evalOS EZero  = EZero   -- value
evalOS ETrue  = ETrue   -- value
evalOS EFalse = EFalse  -- value
evalOS (ESucc e) = ESucc (evalOS e) -- E-Succ
evalOS (EPred EZero)     = EZero                      -- E-PredZero
evalOS (EPred (ESucc t)) = if isnv' t then evalOS t   -- E-PredSucc
                                      else EErr
evalOS (EPred e)         = EPred (evalOS e)           -- E-Pred
evalOS (EIszero EZero) = ETrue                      -- E-IszeroZero
evalOS (EIszero (ESucc e)) = if isnv' e then EFalse -- E-IszeroSucc
                                        else EErr
evalOS (EIf cond th el) with cond
... | ETrue   = evalOS th                         -- E-IfTrue
... | EFalse  = evalOS el                         -- E-IfFalse
... | EZero   = EErr
... | ESucc _ = EErr
... | EPred _ = EErr
... | _       = EIf (evalOS cond) th el -- E-IfIf
evalOS _ = EErr

evalMS : Expr → Expr
{-# TERMINATING #-}
evalMS e = let v = evalOS e in
           if isv' v then v
                     else evalMS v