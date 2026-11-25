import Lean

/-!
The paper uses a public copy of the construction's mathematical definitions.
Several of these definitions are structures. Their public constructors therefore
have different names from the constructors in the original implementation.

This utility instantiates the original Lean proof terms at the public names.
It reuses mathlib declarations and entries that are already public. For the
rest it presents the renamed term to the kernel as an ordinary declaration.
The map of previously published lemmas gives the archive its proof dependencies.
-/
namespace Lax793645Proofs.Manuscript.Publication
open Lean

private abbrev Names := Std.HashMap Name Name
private abbrev CopyM := StateT Names CoreM

private def localConstant (n : Name) : Bool :=
  (`Lax793645Proofs).isPrefixOf (privateToUserName n)

private def dataName (n : Name) : Name :=
  let p := privateToUserName n
  let q := if (`Lax793645Proofs.Upstream.OAI).isPrefixOf p then
    p.replacePrefix `Lax793645Proofs.Upstream.OAI `Lax793645.ConstructionData.Binary
  else
    p.replacePrefix `Lax793645Proofs.Simplifications `Lax793645.ConstructionData.Frames
  if q == p then .anonymous
  else if p == n then q else mkPrivateNameCore `Lax793645.ConstructionData q

private def proofName (n : Name) : Name :=
  `Lax793645Proofs.Manuscript.Terms ++ n

private partial def renameExpr (names : Names) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => (names[n]?).map fun k => .const k ls
    | .proj n i v => some (.proj (names[n]?.getD n) i (renameExpr names v))
    | _ => none

private def remember (a b : Name) : CopyM Unit :=
  modify fun names => names.insert a b

/-- Translate the dependency closure of a declaration. Mutually defined
inductive types must be introduced in one kernel declaration. -/
private partial def copy (n : Name) : CopyM Unit := do
  unless localConstant n do return
  if (← get).contains n then return
  let env ← getEnv
  let publicName := dataName n
  let original ← getConstInfo n
  let publicDecl := env.find? publicName
  if publicDecl.isSome && (original matches .inductInfo _ | .ctorInfo _ | .recInfo _) then
    remember n publicName
    return
  let dst := proofName n
  if env.contains dst then
    remember n dst
    return
  let scan (e : Expr) := e.forEach fun t => do
    match t with
    | .const k _ | .proj k .. => copy k
    | _ => pure ()
  let matchesPublic (e : Expr) (publicType : Expr) (params : List Name) : CopyM Bool := do
    if params.length != original.levelParams.length then return false
    let t := publicType.instantiateLevelParams params (original.levelParams.map Level.param)
    return Kernel.isDefEqGuarded (← getEnv) {} e t
  let checked (d : Declaration) : CopyM Unit := do
    try addDecl d catch error => throwError "While exposing {n}: {error.toMessageData}"
  match original with
  | .ctorInfo v => copy v.induct
  | .recInfo v => for k in v.all do copy k
  | .inductInfo v =>
    let mut origins := #[]
    for k in v.all do
      let info ← getConstInfoInduct k
      origins := origins.push info
      remember k (proofName k)
      remember (k.str "rec") ((proofName k).str "rec")
      for c in info.ctors do remember c (proofName c)
    let mut types := #[]
    for info in origins do
      scan info.type
      let mut ctors := #[]
      for c in info.ctors do
        let ctor ← getConstInfoCtor c
        scan ctor.type
        ctors := ctors.push {name := proofName c, type := renameExpr (← get) ctor.type : Constructor}
      types := types.push {
        name := proofName info.name
        type := renameExpr (← get) info.type
        ctors := ctors.toList : InductiveType}
    checked (.inductDecl v.levelParams v.numParams types.toList false)
  | .defnInfo v =>
    scan v.type
    scan v.value
    let names ← get
    let ty := renameExpr names v.type
    let val := renameExpr names v.value
    if let some (.defnInfo pub) := publicDecl then
      if (← matchesPublic ty pub.type pub.levelParams) &&
          (← matchesPublic val pub.value pub.levelParams) then
        remember n publicName
        return
    if ty == v.type && val == v.value then
      remember n n
      return
    checked (.defnDecl {v with name := dst, type := ty, value := val, all := [dst]})
    remember n dst
  | .thmInfo v =>
    scan v.type
    if let some (.thmInfo pub) := publicDecl then
      if ← matchesPublic (renameExpr (← get) v.type) pub.type pub.levelParams then
        remember n publicName
        return
    scan v.value
    let names ← get
    let ty := renameExpr names v.type
    let val := renameExpr names v.value
    if ty == v.type && val == v.value then
      remember n n
      return
    checked (.thmDecl {v with name := dst, type := ty, value := val, all := [dst]})
    remember n dst
  | _ => throwError "Unsupported construction declaration {n}"

/-- Publish a mathematical result at an explicit type. Its own archive
statement is available only to subsequent proofs in the dependency map. -/
def publish (entries : Array (Name × Name × Name)) : CoreM Unit := do
  let published := entries.foldl (init := ({} : Names)) fun m (src, claim, _) =>
    m.insert src claim
  let mut names := published
  for (src, _, dst) in entries do
    let .thmInfo v ← getConstInfo src | throwError "Expected a theorem at {src}"
    let search : CopyM Unit := do
      for e in #[v.type, v.value] do
        e.forEach fun t => do
          match t with
          | .const k _ | .proj k .. => copy k
          | _ => pure ()
    names := (← search.run names).2
    addDecl (.thmDecl {v with
      name := dst
      type := renameExpr names v.type
      value := renameExpr names v.value
      all := [dst]})

end Lax793645Proofs.Manuscript.Publication
