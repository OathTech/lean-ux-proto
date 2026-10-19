import Leanux.Proofs.WG.Lifetimes.SocketFrames
import Leanux.Proofs.WG.Lifetimes.SavedPeers

/-! Complete loopback calls, including the demanded prefix of the saved-peer
NAPI scan. The remaining record consumer has no resident-object access. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def loopbackFinish : WG.M Unit := do
  modify fun w => { w with netRxRaised := false }
  if (← getAmbient).hidden.isNone then return
  let start := (HiddenSite.sectionStart .netRx).info
  if (← peekHiddenSite) != some start.id then
    let next := match ← peekHiddenSite with | some s => s!"site {s}" | none => "none"
    throw (.hidden s!"a loopback transmission raised NET_RX: expected its section ({start.label}, site {start.id}) at the send's local_bh_enable, the record is {next}")
  _ ← hidden (.sectionStart .netRx)
  skipCut loopbackRxSites
  _ ← hidden (.sectionStop .netRx)

theorem loopbackFinish_sameStore : SameWGStore loopbackFinish := by
  intro initial
  let P := fun w : WGWorld => wgStoreView w = initial
  change Preserves P loopbackFinish
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have stopped (e : Stop) : Preserves P (throw e : WG.M Unit) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' h hr
    cases hr
  have finish : Preserves P (do
      _ ← hidden (.sectionStart .netRx)
      skipCut loopbackRxSites
      _ ← hidden (.sectionStop .netRx) : WG.M Unit) :=
    preserves_bind (ambient (AmbientM.hidden (.sectionStart .netRx))) (fun _ =>
      preserves_bind (ambient (AmbientM.skipCut loopbackRxSites)) (fun _ =>
        preserves_bind (ambient (AmbientM.hidden (.sectionStop .netRx))) (fun _ => preserves_pure ())))
  unfold loopbackFinish
  apply preserves_bind (hoare_modify (fun w : WGWorld => {w with netRxRaised := false}) (fun _ h => h))
  intro _
  apply preserves_bind (ambient (get : AmbientM Ambient))
  intro a
  split
  · exact preserves_pure ()
  · apply preserves_bind (ambient AmbientM.peekHiddenSite)
    intro site
    split
    · apply preserves_bind (ambient AmbientM.peekHiddenSite)
      intro next
      exact preserves_bind (stopped _) (fun _ => finish)
    · exact finish

def loopbackSoftirqPrefix : MixedM Unit := do
  if !(← liftWGPrefix (get : WG.M WGWorld)).netRxRaised then return
  let d ← liftWGPrefix getDev
  if ← savedPeerAny (·.napiScheduled) d.peers.toList then
    liftWGPrefix (unsupported "a loopback NET_RX section while a NAPI poll is pending (one net_rx_action polls both)")
  liftWGPrefix loopbackFinish

theorem loopbackSoftirq_source : loopbackSoftirq = (do
    if !(← get).netRxRaised then return
    let d ← getDev
    let pending ← pure (d.peers.toList.any (·.2.napiScheduled))
    if pending then
      unsupported "a loopback NET_RX section while a NAPI poll is pending (one net_rx_action polls both)"
    loopbackFinish) := by
  simp only [loopbackSoftirq, loopbackFinish, pure_bind]
  congr 1

theorem loopbackSoftirqPrefix_erases : ErasesStatePrefix loopbackSoftirqPrefix loopbackSoftirq := by
  rw [loopbackSoftirq_source]
  unfold loopbackSoftirqPrefix
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro w
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro d
    apply erasesStatePrefix_bind (savedPeerAny_erases _ _)
    intro pending
    split
    · exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_lift _)
    · exact erasesStatePrefix_lift _

theorem loopbackSoftirqPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) :
    AmbientSpec I P loopbackSoftirqPrefix (fun _ => P) := by
  unfold loopbackSoftirqPrefix
  apply StatePrefixEnsures.bind (c.store P get (by intro initial; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)))
  intro w
  split
  · exact c.pure P _
  · apply StatePrefixEnsures.bind (getDev_saved_spec c P)
    intro d
    apply StatePrefixEnsures.bind (savedPeerAny_spec c P _ _)
    intro pending
    split
    · exact StatePrefixEnsures.bind (c.unsupported P _) (fun _ => c.store P _ loopbackFinish_sameStore)
    · exact c.store P _ loopbackFinish_sameStore

def loopbackSendPrefix (sites : List HiddenSite) (raised : Bool) : MixedM Unit := do
  liftWGPrefix (skipCut sites)
  if raised then
    liftWGPrefix raiseLoopbackRx
    loopbackSoftirqPrefix

theorem loopbackSendPrefix_erases (sites : List HiddenSite) (raised : Bool) :
    ErasesStatePrefix (loopbackSendPrefix sites raised) (loopbackSend sites raised) := by
  unfold loopbackSendPrefix loopbackSend
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  split
  · exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => loopbackSoftirqPrefix_erases)
  · exact erasesStatePrefix_pure _

theorem loopbackSendPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (sites : List HiddenSite) (raised : Bool) : AmbientSpec I P (loopbackSendPrefix sites raised) (fun _ => P) := by
  unfold loopbackSendPrefix
  apply StatePrefixEnsures.bind (c.store P _ (fun initial => hoare_liftAmbient (AmbientM.skipCut sites) (fun w => wgStoreView w = initial)))
  intro _
  split
  · exact StatePrefixEnsures.bind (c.store P _ raiseLoopbackRx_sameStore) (fun _ => loopbackSoftirqPrefix_spec c P)
  · exact c.pure P _

/-- Product callers retain arbitrary invariants over all actual components. -/
theorem loopbackSoftirqPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) :
    ProductAmbientSpec I P (liftWGObserver loopbackSoftirqPrefix) (fun _ => P) := by
  simp only [loopbackSoftirqPrefix, liftWGObserver_bind, apply_ite, liftWGObserver_pure]
  apply PrefixEnsures.bind (c.nativeStore P (get : WG.M WGWorld)
    (by intro initial; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)))
  intro w
  split
  · exact c.pure P _
  · apply PrefixEnsures.bind (getDev_saved_spec_product c P)
    intro d
    apply PrefixEnsures.bind (savedPeerAny_spec_product c P _ _)
    intro pending
    split
    · apply PrefixEnsures.bind (c.nativeStore P _
        (fun initial => hoare_liftAmbient (AmbientM.unsupported _)
          (fun w => wgStoreView w = initial)))
      intro _
      exact c.nativeStore P _ loopbackFinish_sameStore
    · exact c.nativeStore P _ loopbackFinish_sameStore

theorem loopbackSendPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (sites : List HiddenSite) (raised : Bool) :
    ProductAmbientSpec I P (liftWGObserver (loopbackSendPrefix sites raised)) (fun _ => P) := by
  simp only [loopbackSendPrefix, liftWGObserver_bind, apply_ite, liftWGObserver_pure]
  apply PrefixEnsures.bind (c.nativeStore P _
    (fun initial => hoare_liftAmbient (AmbientM.skipCut sites)
      (fun w => wgStoreView w = initial)))
  intro _
  split
  · exact PrefixEnsures.bind (c.nativeStore P _ raiseLoopbackRx_sameStore)
      (fun _ => loopbackSoftirqPrefix_spec_product c P)
  · exact c.pure P _

end Leanux.Proofs.WG.Lifetimes
