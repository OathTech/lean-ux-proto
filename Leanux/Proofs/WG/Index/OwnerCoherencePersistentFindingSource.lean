import Leanux.Proofs.WG.Index.OwnerCoherencePersistentFindingModel
import Leanux.Proofs.WG.Index.StagedSource
import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG
open PersistentOwnerWitness

/-- Total execution of the original callback on the witness, for every native
realization of its projected device and real input record. Cleanup removes peer
0 while its separately hashed keypair remains. -/
theorem persistentOwnerWitness_returns :
    Campaign2.Returns (expiredSendPersistentKeepalive 0)
      (fun s => s.wg.device = some device ∧ s.ambient.hidden = some [clock])
      (fun _ s => ∃ final, s.wg.device = some final ∧ final.peers[0]? = none ∧
        final.keypairs[0]? = some dangling ∧ entry ∈ final.indexTable) := by
  intro g ambient pre
  change g.dev = some device ∧ ambient.hidden = some [clock] at pre
  obtain ⟨hd, hh⟩ := pre
  have active : HiddenSite.passive 6 = false := by decide
  have fresh : ¬ ((180 : Nat).toInt64 * (1000000000 : Int64) ≤ 0) := by decide
  have removeForm : indexRemove (.handshake 0) = (do
      _ ← branch .idxRemoveHashed ((← get).any (·.owner == .handshake 0))
      modify fun table => table.filter fun e => !(e.owner == .handshake 0) : IndexM Unit) := rfl
  have lifted : (monadLift (indexRemove (.handshake 0)) : WG.M Unit) =
      liftIndex (indexRemove (.handshake 0)) := rfl
  simp only [expiredSendPersistentKeepalive, sendKeepalive, sendStagedPackets,
    createData, peerPut, lifted]
  simp [
    keypairGet, keypairPut, peerGet, requireNotPending,
    branchExpired, birthdateTest, hiddenClock64, AmbientM.hiddenClock64,
    AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
    HiddenSite.info, active, fresh, Worker.sectionId, Worker.index,
    removeForm, liftIndex, retirePeerUnits, modifyAmbient, PeerTimer.all, Peer.timerPending, Peer.timer, Peer.wheel,
    IndexOwner.peerDeref, IndexOwner.peerWord,
    newTxSkb, freeTxSkb, getTxSkb, liftSkb, SkbStore.newTx, SkbStore.getTx, SkbStore.freeTx,
    getPeer, setPeer, getKeypair, setKeypair, getDev, modifyDev,
    refcountIncNotZero, refcountInc, refcountDecAndTest,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    ipTunnelEcnEncap, ipTunnelGetDsfield, Packet.protocol,
    victim, acquired, dangling, selected, device, entry, clock,
    hd, hh, REJECT_AFTER_TIME, REJECT_AFTER_MESSAGES, COUNTER_WINDOW_SIZE,
    NSEC_PER_SEC64, EINVAL, WG.EPIPE, ETH_P_8021Q, ETH_P_8021AD, ETH_P_IP, ETH_P_IPV6,
    Campaign2.snapshot, Campaign2.core, bind_assoc, Std.TreeMap.getElem_insert]
  refine ⟨(), _, ⟨_, rfl⟩, _, rfl, ?_, ?_, ?_⟩
  · simp
  · simp [Std.TreeMap.getElem_insert]
  · simp


end Leanux.Proofs.WG.Index
