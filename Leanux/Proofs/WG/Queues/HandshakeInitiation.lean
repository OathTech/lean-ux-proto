import Leanux.Proofs.WG.Queues.HandshakeSendResponse

/-! The actual initiation arm carries its acquired reservation through the
response send and the existing final receive payment. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeInitiation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HandshakeResponse

/-- This is the literal post-acquisition part of the initiation arm. -/
def afterLookup (peer : Option PeerId) (src : SkbSource) : WG.M (Option PeerId) := do
  if ← branch .hsInitNoPeer peer.isNone then return none
  let some pid := peer | invariant "unreachable"
  setPeerEndpointFromSkb pid src
  sendHandshakeResponse pid
  pure peer

def branchSource (msg : List UInt8) (src : SkbSource) : WG.M (Option PeerId) :=
  consumeInitiation msg >>= fun peer => afterLookup peer src

/-- The exact old initiation arm before the shared final receive payment. -/
theorem branch_factor (msg : List UInt8) (src : SkbSource) : (do
    let peer ← consumeInitiation msg
    if ← branch .hsInitNoPeer peer.isNone then return none
    let some pid := peer | invariant "unreachable"
    setPeerEndpointFromSkb pid src
    sendHandshakeResponse pid
    pure peer : WG.M (Option PeerId)) = branchSource msg src := rfl

private theorem afterLookup_some (o : Owner) (src : SkbSource) :
    Hoare (afterLookup (some o.slot) src) (Input cs (o::loans))
      (fun peer w => peer=some o.slot ∧ Boundary cs (o::loans) w) := by
  have inner : Hoare (do
      setPeerEndpointFromSkb o.slot src
      sendHandshakeResponse o.slot
      pure (some o.slot) : WG.M (Option PeerId)) (Input cs (o::loans))
      (fun peer w => peer=some o.slot ∧ Boundary cs (o::loans) w) := by
    apply hoare_bind _ _ (endpoint o.slot src)
    intro _
    apply hoare_bind _ _ (HandshakeSendResponse.sendResponse o.slot)
    intro _
    exact hoare_pure _ _
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change ((do
    setPeerEndpointFromSkb o.slot src
    sendHandshakeResponse o.slot
    pure (some o.slot) : WG.M (Option PeerId)).run w).run
      (CounterWindow.record a .hsInitNoPeer false)=.ok ((result,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp inner w _ result v b hi run

theorem branch_spec (msg : List UInt8) (src : SkbSource) :
    Hoare (branchSource msg src) (Input cs loans) (Selected cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  unfold branchSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,consume,tail⟩ := run
  obtain ⟨holders,funded,stable⟩ := hi.1
  have post := HandshakeEntry.initiation_funded msg funded stable hi.2 a c consume
  cases peer with
  | none =>
    change Except.ok ((none,u),CounterWindow.record c .hsInitNoPeer true)=.ok ((result,v),b) at tail
    cases tail
    exact ⟨holders,post.1⟩
  | some pid =>
    obtain ⟨o,slot,funded,stable⟩ := post.1
    subst pid
    have paid := (hoare_iff_run_ambient _ _ _).mp (afterLookup_some o src) u c result v b
      ⟨⟨holders,funded,stable⟩,post.2⟩ tail
    rw [paid.1]
    exact ⟨o,rfl,paid.2⟩

theorem paid (msg : List UInt8) (src : SkbSource) :
    Hoare (branchSource msg src >>= fun peer => HandshakeReceive.finishSelected peer msg)
      (Input cs loans) (fun _ => Boundary cs loans) :=
  hoare_bind _ _ (branch_spec msg src) (fun peer => HandshakeResponse.finish peer msg)

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeInitiation
