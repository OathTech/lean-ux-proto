import Leanux.Proofs.WG.HandshakeSecurity.ResponderCoreFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Origins Origins.Retaining Lifetimes
open Lean Meta Elab Tactic

macro "core_skb " P:term : tactic => `(tactic|
  first
    | (index_material_head getTxSkb; unfold getTxSkb)
    | (index_material_head setTxSkb; unfold setTxSkb)
    | (index_material_head newTxSkb; unfold newTxSkb)
    | (index_material_head freeTxSkb; unfold freeTxSkb)
    | (index_material_head liftSkb
       apply hoare_liftSkb _ (fun w => $P (pool w))
       intro w d store hw hd
       change $P (fun kid => (d.keypairs[kid]?).map keyCore)
       change $P (fun kid => (w.dev.bind fun d => d.keypairs[kid]?).map keyCore) at hw
       rw [hd] at hw
       exact hw))

macro "core_traffic " P:term : tactic => `(tactic|
  first
    | core_skb $P
    | (index_material_head branchExpired; exact ((branchExpired_sameWGWorld _ _ _ _).factor pool).wp $P)
    | (index_material_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor pool).wp $P)
    | (index_material_head cpumaskChooseOnline; exact (pool_of_material (cpumaskChooseOnline_material _)).wp $P)
    | (index_material_head enqueuePerDeviceAndPeer; exact (pool_of_material (enqueuePerDeviceAndPeer_material _ _)).wp $P)
    | (index_material_head keypairGet; exact (keypairGet_core _).wp $P)
    | (run_tac do
         let t ← getMainTarget
         let args := t.getAppArgs
         unless args.size ≥ 3 do throwError "not a contract"
         let head := args[args.size-3]!.getAppFn
         let .const n _ := head | throwError "not a peer modifier"
         unless n.toString.endsWith ".modifyPeer" do throwError "not a peer modifier"
       exact (pool_of_material (modifyPeer_material _ _)).wp $P)
    | (index_material_head WG.orM; unfold WG.orM)
    | (index_material_head WG.andM; unfold WG.andM)
    | core_basic $P)

theorem queued_core (pid : PeerId) (retry : Bool) :
    SameView pool (sendQueuedHandshakeInitiation pid retry) := by
  apply pool_of_material
  intro initial
  unfold sendQueuedHandshakeInitiation
  material_lower
  try unfold recordQueued
  try unfold peekQueuedUnit
  try unfold queueDeviceWork
  repeat' traffic_basic (fun p => p = initial)

theorem publication_core (item : List SkbId) (state : PacketState) :
    SameView pool (enqueuePerPeerTx item state) := by
  apply pool_of_material
  intro initial
  unfold enqueuePerPeerTx
  material_lower
  try unfold recordQueued
  try unfold peekQueuedUnit
  try unfold queueDeviceWork
  repeat' first
    | (index_material_head cpumaskChooseOnline; exact (cpumaskChooseOnline_material _).wp (fun p => p = initial))
    | traffic_basic (fun p => p = initial)

theorem createData_core (pid : PeerId) (item : List SkbId) : CoreRetains (createData pid item) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => Retains initial (pool w))
    (Q := fun _ w => Retains initial (pool w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    rw [h]
    exact Retains.refl _
  unfold createData
  material_lower
  try unfold recordQueued
  try unfold peekQueuedUnit
  try unfold queueDeviceWork
  repeat' first
    | (index_material_head enqueuePerPeerTx; exact (publication_core _ _).wp (Retains initial))
    | (index_material_head keypairPut; exact (keypairPut_core _ _).wp initial)
    | core_traffic (Retains initial)

theorem stagedOutNokey_core (pid : PeerId) (packets : List Packet)
    (kp : Option KeypairId) (invalid : Bool) :
    CoreRetains (stagedOutNokey pid packets kp invalid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => Retains initial (pool w))
    (Q := fun _ w => Retains initial (pool w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    rw [h]
    exact Retains.refl _
  unfold stagedOutNokey
  material_lower
  repeat' first
    | (index_material_head sendQueuedHandshakeInitiation; exact (queued_core _ _).wp (Retains initial))
    | (index_material_head keypairPut; exact (keypairPut_core _ _).wp initial)
    | core_traffic (Retains initial)

theorem sendStagedPackets_core (pid : PeerId) : CoreRetains (sendStagedPackets pid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => Retains initial (pool w))
    (Q := fun _ w => Retains initial (pool w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    rw [h]
    exact Retains.refl _
  unfold sendStagedPackets
  material_lower
  repeat' first
    | traffic_join
    | (index_material_head sendQueuedHandshakeInitiation; exact (queued_core _ _).wp (Retains initial))
    | (index_material_head createData; exact (createData_core _ _).wp initial)
    | (index_material_head keypairPut; exact (keypairPut_core _ _).wp initial)
    | (index_material_head ipTunnelEcnEncap; exact ((ipTunnelEcnEncap_sameWGWorld _).factor pool).wp (Retains initial))
    | (index_material_head List.mapM; apply mapM_view_spec pool (Retains initial); intro pkt)
    | core_traffic (Retains initial)

end Leanux.Proofs.WG.HandshakeSecurity.Responder
