import Leanux.Proofs.WG.Queues.HandshakeEntry
import Leanux.Proofs.WG.Queues.HolderConfigUpdate

/-! The original successful-response arm retains its actual optional lookup
loan, updates the endpoint, runs session/keepalive work and finally pays the
selected owner. Missing acquisitions retain an uncharged None endpoint; the enclosing receive
source returns early on that path. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeResponse
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def Input (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  Boundary cs loans w ∧ HandshakeEntry.Entry w

def Selected (cs : Ledger) (loans : Reservations) (peer : Option PeerId) (w : WGWorld) : Prop :=
  match peer with
  | none => Boundary cs loans w
  | some pid => ∃ o : Owner,o.slot=pid ∧ Boundary cs (o::loans) w

private theorem endpoint_boundary (pid : PeerId) (src : SkbSource) :
    Preserves (Boundary cs loans) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb
       exact HolderEncrypt.native_boundary (HolderEncrypt.store_fields (endpointFromSkb_sameWGStore _)))
    | (rx_retention_head setPeerEndpoint; exact HolderConfigUpdate.endpoint_boundary _ _)
    | handshake_boundary_step

theorem endpoint (pid : PeerId) (src : SkbSource) : Preserves (Input cs loans) (setPeerEndpointFromSkb pid src) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (endpoint_boundary pid src) w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp (HandshakeEntry.endpoint pid src) w a x v b hi.2 run⟩

/-- This is the literal post-acquisition part of the response arm. -/
def afterLookup (peer : Option PeerId) (src : SkbSource) : WG.M (Option PeerId) := do
  if ← branch .hsRespNoPeer peer.isNone then return none
  let some pid := peer | invariant "unreachable"
  setPeerEndpointFromSkb pid src
  HandshakeReceive.responseSession pid
  pure peer

def branchSource (msg : List UInt8) (src : SkbSource) : WG.M (Option PeerId) :=
  consumeResponse msg >>= fun peer => afterLookup peer src

/-- The exact old response arm before the shared final receive payment. -/
theorem branch_factor (msg : List UInt8) (src : SkbSource) : (do
    let peer ← consumeResponse msg
    if ← branch .hsRespNoPeer peer.isNone then return none
    let some pid := peer | invariant "unreachable"
    setPeerEndpointFromSkb pid src
    if ← branch .hsRespSessionBegun (← beginSession pid) then
      timersSessionDerived pid
      timersHandshakeComplete pid
      sendKeepalive pid
    pure peer : WG.M (Option PeerId)) = branchSource msg src := by
  unfold branchSource afterLookup
  apply congrArg (Bind.bind (consumeResponse msg))
  funext peer
  apply congrArg (Bind.bind (branch .hsRespNoPeer peer.isNone : WG.M Bool))
  funext missing
  cases missing <;> cases peer
  all_goals first
    | rfl
    | (apply congrArg (Bind.bind (setPeerEndpointFromSkb _ src)); funext u
       exact HandshakeReceive.responseSession_continuation _ _)

private theorem afterLookup_some (o : Owner) (src : SkbSource) :
    Hoare (afterLookup (some o.slot) src) (Input cs (o::loans))
      (fun peer w => peer=some o.slot ∧ Boundary cs (o::loans) w) := by
  have inner : Hoare (do
      setPeerEndpointFromSkb o.slot src
      HandshakeReceive.responseSession o.slot
      pure (some o.slot) : WG.M (Option PeerId)) (Input cs (o::loans))
      (fun peer w => peer=some o.slot ∧ Boundary cs (o::loans) w) := by
    apply hoare_bind _ _ (endpoint o.slot src)
    intro _
    apply hoare_bind _ _ (hoare_consequence (HandshakeReceive.responseSession_spec o.slot)
      (fun w hi => ⟨hi.1,HandshakeEntry.entry_facts hi.2⟩) (fun _ _ hi => hi))
    intro _
    exact hoare_pure _ _
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change ((do
    setPeerEndpointFromSkb o.slot src
    HandshakeReceive.responseSession o.slot
    pure (some o.slot) : WG.M (Option PeerId)).run w).run
      (CounterWindow.record a .hsRespNoPeer false)=.ok ((result,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp inner w _ result v b hi run

theorem branch_spec (msg : List UInt8) (src : SkbSource) :
    Hoare (branchSource msg src) (Input cs loans) (Selected cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  unfold branchSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,consume,tail⟩ := run
  obtain ⟨holders,funded,stable⟩ := hi.1
  have post := HandshakeEntry.response_funded msg funded stable hi.2 a c consume
  cases peer with
  | none =>
    change Except.ok ((none,u),CounterWindow.record c .hsRespNoPeer true)=.ok ((result,v),b) at tail
    cases tail
    exact ⟨holders,post.1⟩
  | some pid =>
    obtain ⟨o,slot,funded,stable⟩ := post.1
    subst pid
    have paid := (hoare_iff_run_ambient _ _ _).mp (afterLookup_some o src) u c result v b
      ⟨⟨holders,funded,stable⟩,post.2⟩ tail
    rw [paid.1]
    exact ⟨o,rfl,paid.2⟩

theorem finish (peer : Option PeerId) (msg : List UInt8) :
    Hoare (HandshakeReceive.finishSelected peer msg) (Selected cs loans peer)
      (fun _ => Boundary cs loans) := by
  cases peer with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hi run
    cases run
  | some pid =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hi run
    obtain ⟨o,slot,charged⟩ := hi
    subst pid
    exact (hoare_iff_run_ambient _ _ _).mp (HandshakeReceive.finishSelected_spec o msg) w a x v b charged run

/-- The acquired reference remains charged through session and keepalive,
whose real delta is absorbed, then the original final peerPut pays it. -/
theorem paid (msg : List UInt8) (src : SkbSource) :
    Hoare (branchSource msg src >>= fun peer => HandshakeReceive.finishSelected peer msg)
      (Input cs loans) (fun _ => Boundary cs loans) :=
  hoare_bind _ _ (branch_spec msg src) (fun peer => finish peer msg)

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeResponse
