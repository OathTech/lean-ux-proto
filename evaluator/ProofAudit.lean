import Leanux.Proofs.All
import Lean

/- The evaluator owns this file. These examples fix the propositions independently
of candidate theorem declarations. The command runs with Lean trust level zero. -/
example : Leanux.Reference.EventfdRead.StepSimulation
    Leanux.FS.Eventfd.readValue Leanux.FS.Eventfd.eventfdCtxDoRead :=
  Leanux.Proofs.eventfd_step_simulation

example : Leanux.Reference.CloseAliasPreservation :=
  Leanux.Proofs.close_alias_preservation

open Lean Elab Command

private partial def dependencies (env : Environment) (name : Name) :
    StateM (NameSet × NameSet) Unit := do
  if (← get).1.contains name then return
  modify fun (seen, axioms) => (seen.insert name, axioms)
  match env.checked.get.find? name with
  | none => panic! s!"Missing declaration: {name}"
  | some info =>
    match info with
    | .axiomInfo _ => modify fun (seen, axioms) => (seen, axioms.insert name)
    | _ => pure ()
    for dependency in info.type.getUsedConstants do
      dependencies env dependency
    if let some body := info.value? (allowOpaque := true) then
      for dependency in body.getUsedConstants do
        dependencies env dependency
    if let .inductInfo value := info then
      for ctor in value.ctors do dependencies env ctor

elab "#audit_prototype_proofs" : command => do
  let env ← getEnv
  for name in [``Leanux.Proofs.eventfd_step_simulation, ``Leanux.Proofs.close_alias_preservation] do
    let (_, (seen, axioms)) := (dependencies env name).run ({}, {})
    let cached ← collectAxioms name
    let actual := axioms.toArray.qsort Name.lt
    if actual != cached.qsort Name.lt then
      throwError "Direct proof dependency traversal disagrees with Lean's axiom metadata"
    let record := Json.mkObj [
      ("theorem", toJson name.toString),
      ("axioms", toJson (actual.map Name.toString)),
      ("declarations", toJson (seen.toArray.qsort Name.lt |>.map Name.toString))]
    liftIO <| IO.println ("LEANUX_PROOF " ++ record.compress)

#audit_prototype_proofs
