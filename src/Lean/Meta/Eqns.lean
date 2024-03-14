/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ReservedNameAction
import Lean.Meta.Basic
import Lean.Meta.AppBuilder

namespace Lean.Meta
/-- Returns `true` if `name` is of the form `f.eq_<idx>` -/
def isEqnReservedName (name : Name) : Bool :=
  match name with
  | .str p s => !p.isAnonymous && "eq_".isPrefixOf s && (s.drop 3).isNat
  | _ => false

/-- Returns `true` if `name` is of the form `f.def` -/
def isUnfoldReservedName (name : Name) : Bool :=
  match name with
  | .str p "def" => !p.isAnonymous
  | _ => false

/--
Ensures that `f.def` and `f.eq_<idx>` are reserved names if `f` is a safe definition.
-/
builtin_initialize registerReservedNamePredicate fun _ name =>
  isEqnReservedName name || isUnfoldReservedName name

def GetEqnsFn := Name → MetaM (Option (Array Name))

private builtin_initialize getEqnsFnsRef : IO.Ref (List GetEqnsFn) ← IO.mkRef []

/--
Registers a new function for retrieving equation theorems.
We generate equations theorems on demand, and they are generated by more than one module.
For example, the structural and well-founded recursion modules generate them.
Most recent getters are tried first.

A getter returns an `Option (Array Name)`. The result is `none` if the getter failed.
Otherwise, it is a sequence of theorem names where each one of them corresponds to
an alternative. Example: the definition

```
def f (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x::xs => (x+1)::f xs
```
should have two equational theorems associated with it
```
f [] = []
```
and
```
(x : Nat) → (xs : List Nat) → f (x :: xs) = (x+1) :: f xs
```
-/
def registerGetEqnsFn (f : GetEqnsFn) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register equation getter, this kind of extension can only be registered during initialization")
  getEqnsFnsRef.modify (f :: ·)

/-- Returns `true` iff `declName` is a definition and its type is not a proposition. -/
private def shouldGenerateEqnThms (declName : Name) : MetaM Bool := do
  if let some (.defnInfo info) := (← getEnv).find? declName then
    return !(← isProp info.type)
  else
    return false

structure EqnsExtState where
  map    : PHashMap Name (Array Name) := {}
  mapInv : PHashMap Name Name := {} -- TODO: delete?
  deriving Inhabited

/- We generate the equations on demand. -/
builtin_initialize eqnsExt : EnvExtension EqnsExtState ←
  registerEnvExtension (pure {})

/--
Simple equation theorem for nonrecursive definitions.
-/
private def mkSimpleEqThm (declName : Name) (suffix := `def) : MetaM (Option Name) := do
  if let some (.defnInfo info) := (← getEnv).find? declName then
    lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
      let lhs := mkAppN (mkConst info.name <| info.levelParams.map mkLevelParam) xs
      let type  ← mkForallFVars xs (← mkEq lhs body)
      let value ← mkLambdaFVars xs (← mkEqRefl lhs)
      let name := declName ++ suffix
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }
      return some name
  else
    return none

/--
Returns `some declName` if `thmName` is an equational theorem for `declName`.
-/
def isEqnThm? (thmName : Name) : CoreM (Option Name) := do
  return eqnsExt.getState (← getEnv) |>.mapInv.find? thmName

/--
Stores in the `eqnsExt` environment extension that `eqThms` are the equational theorems for `declName`
-/
private def registerEqnThms (declName : Name) (eqThms : Array Name) : CoreM Unit := do
  modifyEnv fun env => eqnsExt.modifyState env fun s => { s with
    map := s.map.insert declName eqThms
    mapInv := eqThms.foldl (init := s.mapInv) fun mapInv eqThm => mapInv.insert eqThm declName
  }

/--
Equation theorems are generated on demand, check whether they were generated in an imported file.
-/
private partial def alreadyGenerated? (declName : Name) : MetaM (Option (Array Name)) := do
  let env ← getEnv
  let eq1 := declName ++ `eq_1
  if env.contains eq1 then
    let rec loop (idx : Nat) (eqs : Array Name) : MetaM (Array Name) := do
      let nextEq := declName ++ (`eq).appendIndexAfter idx
      if env.contains nextEq then
        loop (idx+1) (eqs.push nextEq)
      else
        return eqs
    let eqs ← loop 2 #[eq1]
    registerEqnThms declName eqs
    return some eqs
  else
    return none

/--
Returns equation theorems for the given declaration.
By default, we do not create equation theorems for nonrecursive definitions.
You can use `nonRec := true` to override this behavior, a dummy `rfl` proof is created on the fly.
-/
def getEqnsFor? (declName : Name) (nonRec := false) : MetaM (Option (Array Name)) := withLCtx {} {} do
  if let some eqs := eqnsExt.getState (← getEnv) |>.map.find? declName then
    return some eqs
  else if let some eqs ← alreadyGenerated? declName then
    return some eqs
  else if (← shouldGenerateEqnThms declName) then
    for f in (← getEqnsFnsRef.get) do
      if let some r ← f declName then
        registerEqnThms declName r
        return some r
    if nonRec then
      let some eqThm ← mkSimpleEqThm declName (suffix := `eq_1) | return none
      let r := #[eqThm]
      registerEqnThms declName r
      return some r
  return none

def GetUnfoldEqnFn := Name → MetaM (Option Name)

private builtin_initialize getUnfoldEqnFnsRef : IO.Ref (List GetUnfoldEqnFn) ← IO.mkRef []

/--
Registers a new function for retrieving a "unfold" equation theorem.

We generate this kind of equation theorem on demand, and it is generated by more than one module.
For example, the structural and well-founded recursion modules generate it.
Most recent getters are tried first.

A getter returns an `Option Name`. The result is `none` if the getter failed.
Otherwise, it is a theorem name. Example: the definition

```
def f (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x::xs => (x+1)::f xs
```
should have the theorem
```
(xs : Nat) →
  f xs =
    match xs with
    | [] => []
    | x::xs => (x+1)::f xs
```
-/
def registerGetUnfoldEqnFn (f : GetUnfoldEqnFn) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register equation getter, this kind of extension can only be registered during initialization")
  getUnfoldEqnFnsRef.modify (f :: ·)

/--
Returns an "unfold" theorem for the given declaration.
By default, we do not create unfold theorems for nonrecursive definitions.
You can use `nonRec := true` to override this behavior.
-/
def getUnfoldEqnFor? (declName : Name) (nonRec := false) : MetaM (Option Name) := withLCtx {} {} do
  let env ← getEnv
  let unfoldName := declName ++ `def
  if env.contains unfoldName then
    return some unfoldName
  if (← shouldGenerateEqnThms declName) then
    for f in (← getUnfoldEqnFnsRef.get) do
      if let some r ← f declName then
        unless r == unfoldName do
          throwError "invalid unfold theorem name `{r}` has been generated expected `{unfoldName}`"
        return some r
    if nonRec then
      return (← mkSimpleEqThm declName)
   return none

builtin_initialize
  registerReservedNameAction fun name => do
    if isEqnReservedName name then
      MetaM.run' do return (← getEqnsFor? name.getPrefix).isSome
    else if isUnfoldReservedName name then
      MetaM.run' do return (← getUnfoldEqnFor? name.getPrefix).isSome
    else
      return false

end Lean.Meta
