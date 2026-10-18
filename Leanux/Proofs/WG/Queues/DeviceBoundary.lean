import Leanux.Proofs.WG.Queues.SetPeerBoundary
import Leanux.Proofs.WG.Queues.HolderBaseRetirement
import Leanux.Proofs.WG.Origins.ConfiguredCommand

/-! Native device-configuration removal cuts retain the actual order: the
private-key conflict path pays its lookup loan before retiring the base owner.
These supplied-entry contracts make no initialized funding assertion. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DeviceBoundary
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders Configuration

/-- Paying a named transient reservation preserves the same durable account.
The supplied loan is combined once with all lasting holders. -/
theorem pay_funded (o : Owner) {h : DurableHolders}
    (funded : h.Funded cs (o::loans) w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((peerPut (some o.slot)).run w).run a=.ok (((),v),b)) :
    h.Funded cs loans v ∧ StableRx cs v := by
  have before : CarrierState cs (o::(h.owners++loans)) w :=
    WorkReservations.carrier_loans_perm funded.carriers List.perm_middle
  have after := reservation_payment_stable before stable a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp
    (HolderWorkFrames.peerPut_frame (some o.slot) w) w a () v b (Frame.refl w) run
  exact ⟨⟨funded.aligned.frame frame,after.1⟩,after.2⟩

/-- The source bulk replacement pays every detached base occurrence and
retains the other supplied holders, allowing its real work-queue drains. -/
theorem removeAll : Preserves (fun w => Boundary cs loans w ∧ BaseCoherence.Inv w) peerRemoveAll := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  cases value
  obtain ⟨⟨h,funded,stable⟩,coherent⟩ := hi
  obtain ⟨remaining,_,fundedOut,stableOut⟩ := peerRemoveAll_funded funded stable a b run
  exact ⟨⟨remaining,fundedOut,stableOut⟩,
    (hoare_iff_run_ambient _ _ _).mp BaseCoherence.peerRemoveAll_preserves w a () v b coherent run⟩

/-- This is the actual private-key conflict cut inside deviceKeySource.
Lookup supplies the transient owner; its payment precedes the separate base
retirement exactly as in the source. A missing lookup returns normally. -/
theorem keyConflict (key : Key) :
    Hoare (do
      let peer ← pubkeyLookup key
      if ← branch .setDevOldPeer peer.isSome then
        peerPut peer
        peerRemove peer : WG.M Unit)
      (fun w => Boundary cs loans w ∧ BaseCoherence.Inv w ∧ ConfiguredIdentity.Inv w)
      (fun _ w => Boundary cs loans w ∧ BaseCoherence.Inv w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  cases value
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,lookup,tail⟩ := run
  obtain ⟨⟨h,funded,stable⟩,coherent,configured⟩ := hi
  cases peer with
  | none =>
    obtain ⟨⟨fundedOut,stableOut⟩,coherentOut⟩ :=
      BaseLookupRemoval.lookup_funded key funded stable coherent a c lookup
    change Except.ok (((),u),CounterWindow.record c .setDevOldPeer false)=.ok (((),v),b) at tail
    cases tail
    exact ⟨⟨h,fundedOut,stableOut⟩,coherentOut⟩
  | some pid =>
    obtain ⟨o,slot,fundedOut,stableOut,coherentOut,unique,member⟩ :=
      BaseLookupRemoval.lookup_selected key funded stable coherent configured a c lookup
    subst pid
    change ((peerPut (some o.slot) >>= fun _ => peerRemove (some o.slot)).run u).run
      (CounterWindow.record c .setDevOldPeer true)=.ok (((),v),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,d,payment,removal⟩ := tail
    cases ignored
    obtain ⟨paid,stablePaid⟩ := pay_funded o fundedOut stableOut _ d payment
    have coherentPaid := BaseCoherence.transport coherentOut
      ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.peerPut_view (some o.slot))
        u _ () z d payment)
    obtain ⟨remaining,_,fundedFinal,stableFinal⟩ :=
      peerRemove_some_funded o.slot paid stablePaid unique member d b removal
    exact ⟨⟨remaining,fundedFinal,stableFinal⟩,
      (hoare_iff_run_ambient _ _ _).mp (BaseCoherence.peerRemove_preserves (some o.slot))
        z d () v b coherentPaid removal⟩


/-- The supplied entry invariant needed by each command in a device peer list. -/
def Entry (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  Boundary cs loans w ∧ BaseCoherence.Inv w ∧ ConfiguredIdentity.Inv w

/-- The next command receives configured identity from this same actual run. -/
theorem command (attrs : PeerAttrs) : Preserves (Entry cs loans) (WG.setPeerCmd attrs) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have account := (hoare_iff_run_ambient _ _ _).mp (SetPeerBoundary.setPeerCmd attrs)
    w a result v b hi run
  exact ⟨account.1,account.2,(hoare_iff_run_ambient _ _ _).mp
    (ConfiguredCommand.command attrs) w a result v b hi.2.2 run⟩

/-- Both actual bulk-removal passes retain the complete entry invariant. -/
theorem removeAll_entry : Preserves (Entry cs loans) peerRemoveAll := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have account := (hoare_iff_run_ambient _ _ _).mp removeAll
    w a result v b ⟨hi.1,hi.2.1⟩ run
  exact ⟨account.1,account.2,(hoare_iff_run_ambient _ _ _).mp
    ConfiguredRemoval.removeAll w a result v b hi.2.2 run⟩

/-- The private-key conflict cut also supplies configured identity to its
remaining device continuation, despite either release deleting the peer. -/
theorem keyConflict_entry (key : Key) : Preserves (Entry cs loans) (do
    let peer ← pubkeyLookup key
    if ← branch .setDevOldPeer peer.isSome then
      peerPut peer
      peerRemove peer : WG.M Unit) := by
  have configured : Preserves ConfiguredIdentity.Inv (do
      let peer ← pubkeyLookup key
      if ← branch .setDevOldPeer peer.isSome then
        peerPut peer
        peerRemove peer : WG.M Unit) := by
    apply preserves_bind (ConfiguredRemoval.frame (ConfiguredReceive.pubkeyLookup_view key))
    intro peer
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevOldPeer peer.isSome) ConfiguredIdentity.Inv)
    intro present
    cases present with
    | false => exact preserves_pure ()
    | true =>
      exact preserves_bind (ConfiguredIdentity.peerPut_preserves peer)
        (fun _ => ConfiguredRemoval.remove peer)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have account := (hoare_iff_run_ambient _ _ _).mp (keyConflict key)
    w a result v b hi run
  exact ⟨account.1,account.2,(hoare_iff_run_ambient _ _ _).mp configured w a result v b hi.2.2 run⟩

/-- The original peer-list stage preserves one complete entry invariant
through every command, including malformed entries and negative errno exits. -/
theorem peers (attrs : DeviceAttrs) : Preserves (Entry cs loans) (devicePeersSource attrs) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerCmd; exact command _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Entry cs loans)
       intro x b
       change Preserves (Entry cs loans) _)
    | rx_retention_step

end Leanux.Proofs.WG.Queues.RxCredits.DeviceBoundary
