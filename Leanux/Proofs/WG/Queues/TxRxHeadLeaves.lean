import Leanux.Proofs.WG.Queues.TxStackHead

/-! Concrete receive-completion leaves preserve a saved TX head. The existing
allocation observers carry validity; no new history or operational observer is introduced. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.RxHeadLeaves
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem join (target : SkbId) (state : PacketState) (g : MixedM α) (a : WG.M α)
    (erase : ErasesStatePrefix g a)
    (allocation : StatePrefixPreserves (fun h w _=>AllocationInv h w) LifetimeEvent.Safe g)
    (head : Hoare a (fun w=>Packets.Inv w ∧ HeadState target state w) (fun _=>HeadState target state)) :
    Preserves (StackHead.Inv target state) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi run
  have allocated := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.observed_allocation)
      g a erase allocation) w ambient result v ambient' hi.1 run
  obtain ⟨h,ha⟩ := hi.1
  exact ⟨allocated,(hoare_iff_run_ambient _ _ _).mp head w ambient result v ambient'
    ⟨(pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.bounded) ha,hi.2⟩ run⟩

theorem staged (pid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (sendStagedPackets pid) :=
  join target state (sendStagedPacketsPrefix pid) _ (sendStagedPacketsPrefix_erases pid)
    (sendStagedPacketsPrefix_preserves_ambient allocationAmbient allocationTx pid)
    (StagedHead.send pid target state)

theorem peerPut (peer : Option PeerId) (target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (WG.peerPut peer) := by
  apply join target state (peerPutMixed peer) _ (peerPutMixed_erases peer)
    (peerPutMixed_allocation peer)
  exact hoare_consequence ((peerPut_packets peer).wp (fun s=>∃p,s target=some p ∧ p.state=state))
    (fun _ hi=>hi.2) (fun _ _ hi=>hi)

theorem keyPut (key : Option KeypairId) (now : Bool) (target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (keypairPut key now) := by
  apply join target state (keypairPutPrefix key now) _ (keypairPutPrefix_erases key now)
    (keypairPutPrefix_allocation key now)
  exact hoare_consequence ((keyPut_packets key now).wp (fun s=>∃p,s target=some p ∧ p.state=state))
    (fun _ hi=>hi.2) (fun _ _ hi=>hi)

private theorem received_ready (pid kid target : Nat) (state : PacketState) :
    Preserves (fun w=>Packets.Inv w ∧ HeadState target state w) (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keypairPut
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxStagedHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StagedHead.key_put) target state _ _)
    | staged_head_base target, state

theorem received (pid kid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (receivedWithKeypair pid kid) := by
  apply join target state (receivedWithKeypairPrefix pid kid) _
    (receivedWithKeypairPrefix_erases pid kid) (receivedWithKeypairPrefix_allocation pid kid)
  exact hoare_consequence (received_ready pid kid target state)
    (fun _ hi=>hi) (fun _ _ hi=>hi.2)

private theorem fresh_ready (pid target : Nat) (state : PacketState) :
    Preserves (fun w=>Packets.Inv w ∧ HeadState target state w) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head sendQueuedHandshakeInitiation
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxStagedHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StagedHead.queued) target state _ _)
    | staged_head_base target, state

theorem fresh (pid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (keepKeyFreshRx pid) := by
  apply join target state (keepKeyFreshRxPrefix pid) _ (keepKeyFreshRxPrefix_erases pid)
    (keepKeyFreshRxPrefix_allocation pid)
  exact hoare_consequence (fresh_ready pid target state)
    (fun _ hi=>hi) (fun _ _ hi=>hi.2)

end Leanux.Proofs.WG.Queues.TxDisposition.RxHeadLeaves
