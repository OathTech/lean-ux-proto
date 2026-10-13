import Leanux.Proofs.WG.Lifetimes.SocketFrames

/-! Complete loopback calls, including the demanded prefix of the saved-peer
NAPI scan. The remaining record consumer has no resident-object access. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def loopbackFinish : M Unit := do
  modify fun w => { w with netRxRaised := false }
  if (← get).hidden.isNone then return
  let start := (HiddenSite.sectionStart .netRx).info
  if (← peekHiddenSite) != some start.id then
    let next := match ← peekHiddenSite with | some s => s!"site {s}" | none => "none"
    throw (.hidden s!"a loopback transmission raised NET_RX: expected its section ({start.label}, site {start.id}) at the send's local_bh_enable, the record is {next}")
  _ ← hidden (.sectionStart .netRx)
  skipCut loopbackRxSites
  _ ← hidden (.sectionStop .netRx)

theorem loopbackFinish_sameKernel : SameKernel loopbackFinish := by
  apply sameKernel_of_wp
  intro k
  have hp := sameKernel_wp _ peekHiddenSite_sameKernel (fun s => s = k)
  have hh (site) := sameKernel_wp _ (hidden_sameKernel site) (fun s => s = k)
  have hc := sameKernel_wp _ (skipCut_sameKernel loopbackRxSites) (fun s => s = k)
  mvcgen [loopbackFinish, hp, hh, hc]

def loopbackSoftirqPrefix : MixedM Unit := do
  if !(← liftPrefix (get : M World)).netRxRaised then return
  let d ← liftPrefix getDev
  if ← savedPeerAny (·.napiScheduled) d.peers.toList then
    liftPrefix (unsupported "a loopback NET_RX section while a NAPI poll is pending (one net_rx_action polls both)")
  liftPrefix loopbackFinish

theorem loopbackSoftirq_source : loopbackSoftirq = (do
    if !(← get).netRxRaised then return
    let d ← getDev
    let pending ← pure (d.peers.toList.any (·.2.napiScheduled))
    if pending then
      unsupported "a loopback NET_RX section while a NAPI poll is pending (one net_rx_action polls both)"
    loopbackFinish) := by
  simp only [loopbackSoftirq, loopbackFinish, pure_bind]
  congr 1

theorem loopbackSoftirqPrefix_erases : ErasesPrefix loopbackSoftirqPrefix loopbackSoftirq := by
  rw [loopbackSoftirq_source]
  unfold loopbackSoftirqPrefix
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro w
  split
  · exact erasesPrefix_pure _
  · apply erasesPrefix_bind (erasesPrefix_lift _)
    intro d
    apply erasesPrefix_bind (savedPeerAny_erases _ _)
    intro pending
    split
    · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _)
    · exact erasesPrefix_lift _

theorem loopbackSoftirqPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) :
    AmbientSpec I P loopbackSoftirqPrefix (fun _ => P) := by
  unfold loopbackSoftirqPrefix
  apply PrefixEnsures.bind (c.kernel P get (by intro w x v hr; cases hr; rfl))
  intro w
  split
  · exact c.pure P _
  · apply PrefixEnsures.bind (getDev_saved_spec c P)
    intro d
    apply PrefixEnsures.bind (savedPeerAny_spec c P _ _)
    intro pending
    split
    · exact PrefixEnsures.bind (c.unsupported P _) (fun _ => c.kernel P _ loopbackFinish_sameKernel)
    · exact c.kernel P _ loopbackFinish_sameKernel

def loopbackSendPrefix (sites : List HiddenSite) (raised : Bool) : MixedM Unit := do
  liftPrefix (skipCut sites)
  if raised then
    liftPrefix raiseLoopbackRx
    loopbackSoftirqPrefix

theorem loopbackSendPrefix_erases (sites : List HiddenSite) (raised : Bool) :
    ErasesPrefix (loopbackSendPrefix sites raised) (loopbackSend sites raised) := by
  unfold loopbackSendPrefix loopbackSend
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro _
  split
  · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => loopbackSoftirqPrefix_erases)
  · exact erasesPrefix_pure _

theorem loopbackSendPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (sites : List HiddenSite) (raised : Bool) : AmbientSpec I P (loopbackSendPrefix sites raised) (fun _ => P) := by
  unfold loopbackSendPrefix
  apply PrefixEnsures.bind (c.kernel P _ (skipCut_sameKernel sites))
  intro _
  split
  · exact PrefixEnsures.bind (c.kernel P _ raiseLoopbackRx_sameKernel) (fun _ => loopbackSoftirqPrefix_spec c P)
  · exact c.pure P _

end Leanux.Proofs.WG.Lifetimes
