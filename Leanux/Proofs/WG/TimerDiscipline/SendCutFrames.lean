import Leanux.Proofs.WG.Noise.ComponentFrames
import Leanux.Proofs.WG.TimerDiscipline.InitiationFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The complete loopback action restores the native WG state on normal return.
The intermediate raise/clear writes make this a substantive frame. -/
theorem loopbackSend_spec_wg_variant (P : WGWorld → Prop)
    (sites : List HiddenSite) (raised : Bool) :
    ⦃fun g => ⌜P g⌝⦄ loopbackSend sites raised ⦃⇓? _ g => ⌜P g⌝⦄ := by
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g input result final after pre run
    cases run
    exact pre
  let tail : WG.M Unit := do
    if (← getAmbient).hidden.isNone then return
    let start := (HiddenSite.sectionStart .netRx).info
    if (← peekHiddenSite) != some start.id then
      let next := match ← peekHiddenSite with | some s => s!"site {s}" | none => "none"
      throw (.hidden s!"a loopback transmission raised NET_RX: expected its section ({start.label}, site {start.id}) at the send's local_bh_enable, the record is {next}")
    _ ← hidden (.sectionStart .netRx)
    skipCut loopbackRxSites
    _ ← hidden (.sectionStop .netRx)
  have tailFrame : Ensures tail P (fun _ => P) := by
    unfold tail
    refine ensures_bind _ _ (ambient (get : AmbientM Ambient)) ?_
    intro inputs
    split
    · exact hpure ()
    · refine ensures_bind _ _ (ambient AmbientM.peekHiddenSite) ?_
      intro site
      split
      · refine ensures_bind _ _ (ambient AmbientM.peekHiddenSite) ?_
        intro next g input result final after pre run
        cases next <;> cases run
      · refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStart .netRx))) ?_
        intro _
        refine ensures_bind _ _ (ambient (AmbientM.skipCut loopbackRxSites)) ?_
        intro _
        refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStop .netRx))) ?_
        intro _
        exact hpure ()
  have raisedFrame : Ensures (do raiseLoopbackRx; loopbackSoftirq) P (fun _ => P) := by
    intro g input result final after pre run
    cases pending : g.netRxRaised with
    | true =>
      simp [raiseLoopbackRx, pending, invariant, AmbientM.invariant] at run
      cases run
    | false =>
      have raisedRun : ((raiseLoopbackRx.run g).run input) =
          .ok (((), {g with netRxRaised := true}), input) := by
        simp [raiseLoopbackRx, pending]
        rfl
      change (((raiseLoopbackRx.run g).run input) >>= fun ((_, current), inputs) =>
        (loopbackSoftirq.run current).run inputs) = _ at run
      rw [raisedRun] at run
      change ((loopbackSoftirq.run {g with netRxRaised := true}).run input) = _ at run
      have source : loopbackSoftirq = (do
          if !(← get).netRxRaised then return
          if (← getDev).peers.toList.any (·.2.napiScheduled) then
            unsupported "a loopback NET_RX section while a NAPI poll is pending (one net_rx_action polls both)"
          modify fun w => {w with netRxRaised := false}
          tail : WG.M Unit) := rfl
      have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
          (state : WGWorld) (inputs : Ambient) :
          (((action >>= next).run state).run inputs) =
            (((action.run state).run inputs) >>= fun ((value, current), after) =>
              ((next value).run current).run after) := rfl
      have getRun (state : WGWorld) (inputs : Ambient) :
          (((get : WG.M WGWorld).run state).run inputs) = .ok ((state, state), inputs) := rfl
      have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
          (Except.ok value >>= next) = next value := rfl
      rw [source] at run
      simp only [bindRun, getRun, okBind, Bool.not_true, Bool.false_eq_true, ite_false] at run
      cases device : g.dev with
      | none =>
        simp [getDev, device, invariant, AmbientM.invariant] at run
        cases run
      | some d =>
        have read : ((getDev.run {g with netRxRaised := true}).run input) =
            .ok ((d, {g with netRxRaised := true}), input) := by
          simp [getDev, device]
          rfl
        rw [read] at run
        change (((if d.peers.toList.any (·.2.napiScheduled) then do
          unsupported "a loopback NET_RX section while a NAPI poll is pending (one net_rx_action polls both)"
          modify fun w => {w with netRxRaised := false}
          tail
        else do
          modify fun w => {w with netRxRaised := false}
          tail : WG.M Unit).run {g with netRxRaised := true}).run input) = _ at run
        cases napi : d.peers.toList.any (·.2.napiScheduled) with
        | true =>
          simp [napi, unsupported, AmbientM.unsupported] at run
          cases run
        | false =>
          simp only [napi] at run
          have restored : {g with netRxRaised := false} = g := by
            cases g
            simp_all
          change (tail.run {g with netRxRaised := false}).run input = _ at run
          rw [restored] at run
          exact tailFrame g input result final after pre run
  apply (ensures_iff _ _ _).mp
  unfold loopbackSend
  refine ensures_bind _ _ (ambient (AmbientM.skipCut sites)) ?_
  intro _
  cases raised with
  | false => exact hpure ()
  | true => exact raisedFrame

/-- The original arbitrary Kernel predicate is retained over all four owners.
Using the whole WGWorld also preserves the seven former Kernel WG fields. -/
theorem loopbackSend_spec_kernel_variant
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop)
    (sites : List HiddenSite) (raised : Bool) :
    ⦃fun w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ liftWG (loopbackSend sites raised)
      ⦃⇓? _ w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  intro initial result final pre run
  change (((loopbackSend sites raised).run initial.wg).run initial.ambient >>=
    fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _ at run
  cases native : ((loopbackSend sites raised).run initial.wg).run initial.ambient with
  | error stop => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, inputs⟩ := pair
    rw [native] at run
    cases run
    exact (ensures_iff _ _ _).mpr
      (loopbackSend_spec_wg_variant (fun g => P g initial.fs initial.tasks initial.seccomp) sites raised)
      initial.wg initial.ambient result current inputs pre native

end Leanux.Proofs.WG.TimerDiscipline
