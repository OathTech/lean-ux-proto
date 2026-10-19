import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalCallerSource
import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalEffects

/-! Group the actual beginSession/branch/derived-hook source cut and prove its exact receipt adjacency on every outcome. The original state cut agrees across the branch log; no stopped successor state is invented. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Origins

def sessionDerived (site : Decision) (pid : PeerId) : Obs Bool := do
  let begun ← session pid
  let proceed ← liftWGPrefix (branch site begun)
  if proceed then hook .sessionDerived pid
  pure proceed
theorem sessionDerived_exact (site : Decision) (pid : PeerId)
    (g : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (sessionDerived site pid) g a h =
      match ((beginSession pid).run g).run a with
      | .error stop => (.error stop,h)
      | .ok ((begun,next),inputs) =>
        let afterBranch := {inputs with steps:=inputs.steps.push ({decision:=site,outcome:=begun,netRx:=inputs.netRxSection})}
        let sessionReceipt : SessionReceipt :=
          ⟨pid,Campaign2.snapshot g a,begun,Campaign2.snapshot next inputs⟩
        if begun then
          let out:=((timersSessionDerived pid).run next).run afterBranch
          (out.map (fun ((_,last),after)=>((true,last),after)),
            h++[.session sessionReceipt,
              .hook ⟨.sessionDerived,pid,Campaign2.snapshot next afterBranch,
                Campaign2.observeResult out⟩])
        else (.ok ((false,next),afterBranch),h++[.session sessionReceipt]) := by
  unfold sessionDerived
  rw [show runWGPrefix=runStatePrefix from rfl,runStatePrefix_bind]
  have actual:=session_exact pid g a h
  change runStatePrefix _ _ _ _=_ at actual
  rw [actual]
  cases run : ((beginSession pid).run g).run a with
  | error stop => rfl
  | ok out =>
    obtain ⟨⟨begun,next⟩,inputs⟩:=out
    cases begun with
    | false => rfl
    | true =>
      dsimp only
      rw [runStatePrefix_bind]
      change runStatePrefix (do hook .sessionDerived pid; pure true) next
        {inputs with steps:=inputs.steps.push ({decision:=site,outcome:=true,netRx:=inputs.netRxSection})}
        (h++[.session ⟨pid,Campaign2.snapshot g a,true,Campaign2.snapshot next inputs⟩])=_
      rw [runStatePrefix_bind]
      have eq:=hook_exact .sessionDerived pid next
        {inputs with steps:=inputs.steps.push ({decision:=site,outcome:=true,netRx:=inputs.netRxSection})}
        (h++[.session ⟨pid,Campaign2.snapshot g a,true,Campaign2.snapshot next inputs⟩])
      change runStatePrefix _ _ _ _=_ at eq
      rw [eq]
      simp only [HookJournal.action]
      cases ((timersSessionDerived pid).run next).run
        {inputs with steps:=inputs.steps.push ({decision:=site,outcome:=true,netRx:=inputs.netRxSection})} with
      | error stop => simp only [Except.map,List.append_assoc,ite_true,List.cons_append,List.nil_append]
      | ok out =>
        obtain ⟨⟨value,last⟩,after⟩:=out
        cases value
        simp only [runStatePrefix_pure,Except.map,List.append_assoc,ite_true,List.cons_append,List.nil_append]

theorem session_gate_factor {α : Type} (site : Decision) (pid : PeerId) (yes no : Obs α) :
    (do
      let begun ← session pid
      if ← liftWGPrefix (branch site begun) then
        hook .sessionDerived pid
        yes
      else no) =
    (do
      let proceed ← sessionDerived site pid
      if proceed then yes else no) := by
  simp only [sessionDerived,bind_assoc]
  apply bind_congr
  intro begun
  apply bind_congr
  intro proceed
  cases proceed <;> simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind,bind_assoc]
theorem response_pair_source (pid : PeerId) :
    response pid = (do
      let now ← ops.step (hiddenClock64 .respLastSent)
      ops.modifyPeer pid fun p=>{p with lastSentHandshake:=now}
      let created ← ops.create pid
      if ← ops.step (branch .respCreated created.isSome) then
        let some msg:=created | ops.step (invariant "unreachable")
        let msg ← ops.mac pid msg
        let begun ← sessionDerived .respSessionBegun pid
        if begun then
          ops.traversal pid
          ops.sent pid
          let now ← ops.step (hiddenClock64 .respLastSentAgain)
          ops.modifyPeer pid fun p=>{p with lastSentHandshake:=now}
          ops.send pid msg) := by
  unfold response HandshakeSources.responseWith
  simp only [ops,session_gate_factor]
  rfl

theorem hook_paired (kind : HookJournal.Hook) (pid : PeerId)
    (other : kind≠.sessionDerived) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (hook kind pid) := by
  intro g a h prior
  have eq:=hook_exact kind pid g a h
  change runPrefix ((hook kind pid).run g) a h=_ at eq
  rw [eq]
  have paired := Paired.quiet
    (⟨kind,pid,Campaign2.snapshot g a,Campaign2.observeResult (((HookJournal.action kind pid).run g).run a)⟩)
    prior other
  refine ⟨[_],rfl,paired,?_⟩
  cases run : ((HookJournal.action kind pid).run g).run a with
  | error _ => trivial
  | ok out =>
    obtain ⟨⟨value,next⟩,inputs⟩:=out
    simpa only [run] using paired
theorem sessionDerived_paired (site : Decision) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (sessionDerived site pid) := by
  intro g a h prior
  have eq:=sessionDerived_exact site pid g a h
  change runPrefix ((sessionDerived site pid).run g) a h=_ at eq
  rw [eq]
  cases run : ((beginSession pid).run g).run a with
  | error stop => exact ⟨[],by simp,prior,True.intro⟩
  | ok out =>
    obtain ⟨⟨begun,next⟩,inputs⟩:=out
    cases begun with
    | false =>
      have paired:=Paired.refused
        (⟨pid,Campaign2.snapshot g a,false,Campaign2.snapshot next inputs⟩) prior rfl
      exact ⟨[_],rfl,paired,paired⟩
    | true =>
      dsimp only
      have counter := SessionReceipt.Valid.counter
        (r:=⟨pid,Campaign2.snapshot g a,true,Campaign2.snapshot next inputs⟩)
        ⟨g,a,next,inputs,rfl,rfl,run⟩
      have paired := Paired.derived
        (⟨pid,Campaign2.snapshot g a,true,Campaign2.snapshot next inputs⟩)
        (⟨.sessionDerived,pid,Campaign2.snapshot next
          {inputs with steps:=inputs.steps.push ({decision:=site,outcome:=true,netRx:=inputs.netRxSection})},
          Campaign2.observeResult (((timersSessionDerived pid).run next).run
            {inputs with steps:=inputs.steps.push ({decision:=site,outcome:=true,netRx:=inputs.netRxSection})})⟩)
        prior ⟨rfl,rfl,rfl,rfl,counter⟩
      refine ⟨[_,_],rfl,paired,?_⟩
      cases result : ((timersSessionDerived pid).run next).run
        {inputs with steps:=inputs.steps.push ({decision:=site,outcome:=true,netRx:=inputs.netRxSection})} with
      | error _ => trivial
      | ok out =>
        obtain ⟨⟨value,last⟩,after⟩:=out
        simpa only [result,Except.map,ite_true] using paired
theorem lift_paired {α : Type} (a : WG.M α) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ prior=>prior) (fun _ _ _ _ _ _ prior _=>prior)
theorem pure_paired {α : Type} (x : α) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (pure x : Obs α) :=
  StatePrefixEnsures.pure x (fun _ _ _ prior=>prior) (fun _ _ _ prior=>prior)
theorem response_paired (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (response pid) := by
  rw [response_pair_source]
  dsimp (config:={zeta:=false}) only [ops]
  change StatePrefixEnsures _ _ _ (fun _ h _ _=>Paired h)
  repeat' first
    | (maintenance_head sessionDerived; exact sessionDerived_paired _ _)
    | (maintenance_head hook; apply hook_paired; intro equal; cases equal)
    | (maintenance_head liftWGPrefix; exact lift_paired _)
    | (maintenance_head Pure.pure; exact pure_paired _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q:=fun _ h _ _=>Paired h))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction

theorem afterMac_paired (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (afterMac msg src loaded mac) := by
  unfold afterMac HandshakeSources.afterMacWith
  simp (config:={zeta:=false}) only [←response_eq]
  dsimp (config:={zeta:=false}) only [ops]
  change StatePrefixEnsures _ _ _ (fun _ h _ _=>Paired h)
  repeat' first
    | (maintenance_head response; exact response_paired _)
    | (maintenance_head sessionDerived; exact sessionDerived_paired _ _)
    | (maintenance_head hook; apply hook_paired; intro equal; cases equal)
    | (maintenance_head liftWGPrefix; exact lift_paired _)
    | (maintenance_head Pure.pure; exact pure_paired _)
    | (rw [session_gate_factor]; apply StatePrefixEnsures.bind (sessionDerived_paired _ _))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q:=fun _ h _ _=>Paired h))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction
theorem reception_paired (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired (reception msg src) := by
  unfold reception HandshakeSources.receptionWith
  apply StatePrefixEnsures.bind (lift_paired _)
  intro cookie
  split
  · exact StatePrefixEnsures.bind (lift_paired _) (fun _=>pure_paired _)
  · apply StatePrefixEnsures.bind (lift_paired _)
    intro loaded
    apply StatePrefixEnsures.bind (lift_paired _)
    intro mac
    exact afterMac_paired msg src loaded mac
theorem step_paired :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired step := by
  unfold step HandshakeSources.stepWith
  apply StatePrefixEnsures.bind (lift_paired _)
  intro d
  cases d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none => exact StatePrefixEnsures.bind (lift_paired _) (fun _=>pure_paired _)
    | some packet =>
      obtain ⟨msg,src⟩:=packet
      apply StatePrefixEnsures.bind (lift_paired _)
      intro _
      apply StatePrefixEnsures.bind (lift_paired _)
      intro _
      apply StatePrefixEnsures.bind (reception_paired msg src)
      intro _
      exact StatePrefixEnsures.bind (lift_paired _) (fun _=>pure_paired _)

def inspect {α : Type} (observer : Obs α) : WG.M (Inspection α) := fun g ambient =>
  let result:=runWGPrefix observer g ambient []
  .ok (((Campaign2.observeResult result.1,result.2),g),ambient)
theorem inspect_source {α : Type} (observer : Obs α) (original : WG.M α)
    (erase : ErasesStatePrefix observer original) :
    (do let result←inspect observer;pure result.1)=Campaign2.inspect original := by
  funext g a
  change Except.ok ((Campaign2.observeResult (runWGPrefix observer g a []).1,g),a)=_
  have eq : (runWGPrefix observer g a []).1=((original.run g).run a):=erase g a []
  rw [eq]
  rfl
theorem inspect_facts {α : Type} (observer : Obs α)
    (valid : StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory observer)
    (paired : StatePrefixPreserves (fun h _ _=>Paired h) Paired observer) :
    Campaign2.Returns (inspect observer) (fun _=>True)
      (fun result _=>ValidHistory result.2 ∧ Paired result.2 ∧
        ∀serial,result.2.countP (fun e=>e.sessionId==some serial)=
          result.2.countP (fun e=>e.derivedId==some serial)) := by
  intro g a _
  obtain ⟨_,_,hv,_⟩:=valid g a [] (by intro e member;cases member)
  obtain ⟨_,_,hp,_⟩:=paired g a [] Paired.nil
  exact ⟨_,g,a,rfl,hv,hp,fun serial=>hp.counts serial⟩

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
