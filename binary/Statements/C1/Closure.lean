import StatementC1Vacuity
import Lean

/-! Measurement only (run by `measure-surface.py`): the transitive closure of
the declarations a statement mentions (structure fields included), counted
by the module that declares them, leaving out Lean's own libraries and
compiler-generated auxiliaries. -/
open Lean Elab Command

partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
    match env.find? n with
    | none => closure env rest seen
    | some info =>
      let used := info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]
      let ctors := match info with
        | .inductInfo i => i.ctors
        | _ => []
      closure env (ctors ++ used.toList ++ rest) (seen.insert n)

elab "#closure " id:ident : command => do
  let env ← getEnv
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let mut counts : Std.HashMap String Nat := {}
  for n in (closure env [root] {}).toList do
    -- hand-written declarations only: no constructors, recursors, matchers, derived instances
    if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || (env.find? n matches some (.ctorInfo _))
        || (env.find? n matches some (.recInfo _)) || (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome then continue
    let last := n.getString!
    if last.startsWith "inst" || ["ctorIdx","toCtorIdx","ofNat","sizeOf_spec","injEq","inj","noConfusionType","casesOn","recOn"].contains last
        || (last.splitOn "_").length > 1 && last.endsWith "eq_1" then continue
    let some index := env.getModuleIdxFor? n | continue
    let module := env.header.moduleNames[index.toNat]!
    let top := module.getRoot.toString
    if ["Init","Std","Lean"].contains top then continue
    let group := if top == "Leanux" then module.toString else if top == "Kraken" then "Kraken" else
      if top.startsWith "StatementC1" then "C1 statements" else "binary package"
    counts := counts.insert group (counts.getD group 0 + 1)
  let rows := counts.toList.toArray.qsort (fun a b => a.2 > b.2)
  logInfo m!"{root}: {rows.foldl (fun n r => n + r.2) 0} constants outside Lean's libraries; {rows.toList}"

#closure Binary.Statements.C1.Headline
#closure Binary.Statements.C1.Signed
#closure Binary.Statements.C1.Premises
#closure Binary.Statements.C1.HeadlineExplicit
