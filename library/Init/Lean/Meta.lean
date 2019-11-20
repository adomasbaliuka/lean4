/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic
import Init.Lean.Meta.WHNF
import Init.Lean.Meta.InferType
import Init.Lean.Meta.FunInfo
import Init.Lean.Meta.LevelDefEq
import Init.Lean.Meta.ExprDefEq

namespace Lean
namespace Meta

/- =========================================== -/
/- BIG HACK until we add `mutual` keyword back -/
/- =========================================== -/
inductive MetaOp
| whnfOp | inferTypeOp | isDefEqOp | synthPendingOp

open MetaOp

private def exprToBool : Expr → Bool
| Expr.sort _ _ => false
| _             => true

private def boolToExpr : Bool → Expr
| false => mkSort levelZero
| true  => mkBVar 0
private partial def auxFixpoint : MetaOp → Expr → Expr → MetaM Expr
| op, e₁, e₂ =>
  let whnf         := fun e     => auxFixpoint whnfOp e e;
  let inferType    := fun e     => auxFixpoint inferTypeOp e e;
  let isDefEq      := fun e₁ e₂ => exprToBool <$> auxFixpoint isDefEqOp e₁ e₂;
  let synthPending := fun e     => exprToBool <$> auxFixpoint synthPendingOp e e;
  match op with
  | whnfOp         => whnfAux inferType isDefEq synthPending e₁
  | inferTypeOp    => inferTypeAux whnf e₁
  -- | isDefEqOp      => boolToExpr <$> isExprDefEqAux whnf synthPending e₁ e₂
  | isDefEqOp      => boolToExpr <$> pure false
  | synthPendingOp => boolToExpr <$> pure false -- TODO

def whnf (e : Expr) : MetaM Expr :=
auxFixpoint whnfOp e e

def inferType (e : Expr) : MetaM Expr :=
auxFixpoint inferTypeOp e e

def isDefEq (e₁ e₂ : Expr) : MetaM Bool :=
try $ exprToBool <$> auxFixpoint isDefEqOp e₁ e₂
/- =========================================== -/
/-          END OF BIG HACK                    -/
/- =========================================== -/

def isProp (e : Expr) : MetaM Bool :=
isPropAux whnf e

def getFunInfo (fn : Expr) : MetaM FunInfo :=
getFunInfoAux whnf fn

def getFunInfoNArgs (fn : Expr) (nargs : Nat) : MetaM FunInfo :=
getFunInfoNArgsAux whnf fn nargs

/-- Throws exception if `e` is not type correct. -/
def check (e : Expr) : MetaM Unit :=
checkAux whnf isDefEq e

def isTypeCorrect (e : Expr) : MetaM Bool :=
isTypeCorrectAux whnf isDefEq e

end Meta
end Lean
