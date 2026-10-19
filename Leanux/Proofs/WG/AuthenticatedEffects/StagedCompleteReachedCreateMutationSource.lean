import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointMutation

/-! Literal mutation continuations need no accounting hypothesis. Their
fixed native prefixes retain the original pending observer emissions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateMutation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes CausalJournal
open HandshakeSecurity.StagedDisposal CreatePoints AllocatedObligation RetirementSecurity

theorem mark_source {skb : SkbId} {packetState : PacketState}
    (device : w.wg.dev=some d) (resident : d.txSkbs[skb]?=some packet) :
    runPrefix (Admission.actualOps.access (setTxSkbPrefix skb fun p=>{p with state:=packetState})) w h=
      runPrefix (markDue w skb) (markedWorld w d skb packet packetState) (markedHistory w skb h) := by
  rw [mark_access_run device resident]
  rfl

theorem queue_native (device : w.wg.dev=some d) :
    runPrefix (queuePrefix pid peer items) w h=
      (.ok ((),{w with wg:=replacePeer w.wg d pid {peer with txQueue:=peer.txQueue.enqueue items}}),h) := by
  rw [queuePrefix,runPrefix_lift,liftWG_run,install_native pid peer items device]
  rfl

theorem queue_source (device : w.wg.dev=some d) :
    runPrefix (queueInstall pid peer items) w h=
      runPrefix (queueDue pid peer items)
        {w with wg:=replacePeer w.wg d pid {peer with txQueue:=peer.txQueue.enqueue items}} h := by
  rw [queueInstall,runPrefix_bind,queue_write_run device]
  rw [queueDue,runPrefix_bind,runPrefix_emit]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateMutation
