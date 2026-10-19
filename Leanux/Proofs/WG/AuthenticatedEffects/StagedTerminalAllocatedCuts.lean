import Leanux.Proofs.WG.AuthenticatedEffects.StagedAllocationLineage

/-! Allocated first terminals bind the exact pending ticket and allocation to
the current native receipt. These local contracts do not infer the caller's
packet selection or a complete driver history from native validity alone. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal HandshakeSecurity.StagedConservation

private theorem single_pending (pending : (ticket,Status.pending location) ∈ ledger) :
    ∀ t ∈ [ticket], t ∈ pendingAt location ledger := by
  intro t member
  have same := List.mem_singleton.mp member
  subst t
  exact mem_pendingAt.mpr pending

theorem socket (r : Completion.SocketReceipt) (native : r.Valid)
    (valid : Valid domain ledger) (before : Justified history ledger)
    (links : AllocationLinks history ledger) (resident : Resident history ledger r.packet.before.wg)
    (pending : (ticket,Status.pending (.allocated batch ordinal)) ∈ ledger)
    (origin : Origin history batch ordinal generation r.id material) :
    let outcome := Staged.Obligations.Terminal.socket history.length (r.socket.value == 0)
    Staged.Obligations.Step ledger (settle [ticket] outcome ledger) ∧
      Justified (history ++ [.old (.socket r)]) (settle [ticket] outcome ledger) := by
  apply settle_at valid before (single_pending pending)
  intro t member
  have same := List.mem_singleton.mp member
  subst t
  exact .socket r native batch ordinal generation material
    ((links ticket batch ordinal pending).at_origin origin) (resident ticket batch ordinal pending)

/-- A false send result is not enough: the actual send-entry peer read must
select neither socket family. Inner socket errno is already terminal earlier. -/
theorem refused (r : SendResult.Receipt) (native : r.Valid) (failed : r.run.value = false)
    (peer : RunWitness Peer) (read : peer.Valid (liftWG (getPeer r.pid)))
    (entry : peer.before = r.run.before)
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6)
    (valid : Valid domain ledger) (before : Justified history ledger)
    (links : AllocationLinks history ledger) (resident : Resident history ledger r.packet.before.wg)
    (pending : (ticket,Status.pending (.allocated batch ordinal)) ∈ ledger)
    (origin : Origin history batch ordinal generation r.skb material) :
    let outcome := Staged.Obligations.Terminal.sendRefused history.length
    Staged.Obligations.Step ledger (settle [ticket] outcome ledger) ∧
      Justified (history ++ [.sendResult r]) (settle [ticket] outcome ledger) := by
  apply settle_at valid before (single_pending pending)
  intro t member
  have same := List.mem_singleton.mp member
  subst t
  exact .refused r native failed peer read entry not4 not6 batch ordinal generation material
    ((links ticket batch ordinal pending).at_origin origin) (resident ticket batch ordinal pending)

theorem disposed (r : Terminal.Receipt) (native : r.Valid)
    (valid : Valid domain ledger) (before : Justified history ledger)
    (links : AllocationLinks history ledger) (resident : Resident history ledger r.run.before.wg)
    (pending : (ticket,Status.pending (.allocated batch ordinal)) ∈ ledger)
    (origin : Origin history batch ordinal generation r.skb material) :
    let outcome := Staged.Obligations.Terminal.disposed history.length r.reason
    Staged.Obligations.Step ledger (settle [ticket] outcome ledger) ∧
      Justified (history ++ [.terminalDrop r]) (settle [ticket] outcome ledger) := by
  apply settle_at valid before (single_pending pending)
  intro t member
  have same := List.mem_singleton.mp member
  subst t
  exact .disposed r native batch ordinal generation material
    ((links ticket batch ordinal pending).at_origin origin) (resident ticket batch ordinal pending)

/-- Cleanup of an already terminal ticket appends evidence without changing
its first disposition. No pending-cell ownership or free safety is inferred. -/
theorem cleanup (before : Justified history ledger) (r : Terminal.Receipt) :
    Justified (history ++ [.terminalDrop r]) ledger := before.append _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
