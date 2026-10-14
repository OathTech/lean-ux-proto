import Leanux.Proofs.WG.Queues.RxTxFrames

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The complete original receive-completion call retains every surviving
receive queue. This projection theorem does not assert delivery, ownership,
access-prefix completeness, or a retained World after an exception. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem lookup_rxQueues (root : Option NodeId) (bits key : Nat) :
    SameView rxQueues (lookup root bits key) := by
  apply SameView.of_wp
  intro s
  have hs := (rxQueues_kernel (swapEndian_sameKernel bits)).wp (fun t => t = s)
  have hf := (rxQueues_kernel (findNode_sameKernel root bits key)).wp (fun t => t = s)
  have hn := fun id => (rxQueues_kernel (Framing.getNode_sameKernel id)).wp (fun t => t = s)
  have hp := fun pid => (peerGetMaybeZero_rxQueues pid).wp (fun t => t = s)
  mvcgen [lookup, hs, hf, hn, hp, branch, invariant, unsupported]

theorem lookupSrc_rxQueues (protocol : Nat) (bytes : List UInt8) :
    SameView rxQueues (lookupSrc protocol bytes) := by
  apply SameView.of_wp
  intro s
  have hl := fun root bits key => (lookup_rxQueues root bits key).wp (fun t => t = s)
  mvcgen [lookupSrc, hl, getDev, getK, branch, invariant]

theorem dishonest_rxQueues (why : Dishonest) : SameView rxQueues (dishonest why) :=
  modifyDev_rxQueues _ (fun d => by cases why <;> rfl) (fun d => by cases why <;> rfl)

theorem updateRxStats_rxQueues (pid : PeerId) (len : Nat) :
    SameView rxQueues (updateRxStats pid len) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hd := (modifyDev_rxQueues (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [updateRxStats, hg, hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem consumeDataDone_rxQueues (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsRx (consumeDataDone pid pkt endpoint) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hep := (setPeerEndpoint_rxQueues pid endpoint).wp P
  have hk := (receivedWithKeypair_rxQueues pid pkt.keypair).wp P
  have hh := (timersHandshakeComplete_rxQueues pid .walltimeLastHandshakeData).wp P
  have hst := (sendStagedPackets_rxQueues pid).wp s
  have hf := (keepKeyFreshRx_rxQueues pid).wp s
  have ha := (timersAnyAuthenticatedPacketReceived_rxQueues pid).wp P
  have htr := (timersTraversal_rxQueues pid).wp P
  have hdata := (timersDataReceived_rxQueues pid).wp P
  have hstats := fun len => (updateRxStats_rxQueues pid len).wp P
  have herr := fun why => (dishonest_rxQueues why).wp P
  have hecn := fun protocol outer bytes => (rxQueues_kernel (inetEcnDecapsulate_sameKernel protocol outer bytes)).wp P
  have hl := fun protocol bytes => (lookupSrc_rxQueues protocol bytes).wp P
  have hp := fun peer => (peerPut_rxQueues peer).wp s
  mvcgen [consumeDataDone, hep, hk, hh, hst, hf, ha, htr, hdata, hstats, herr, hecn, hl, hp,
    WG.andM, WG.orM, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all)
  all_goals subst s
  all_goals exact rx_retained_refl _

end Leanux.Proofs.WG.Queues
