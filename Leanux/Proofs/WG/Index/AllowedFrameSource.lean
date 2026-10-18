import Leanux.Proofs.WG.Config.AllowedTransferOperations
import Leanux.Proofs.WG.Queues.SlotConfiguration
import Leanux.Proofs.Framing.WGDump

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.AllowedFrame
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Lifetimes Std.Do Queues

/-- Mutable leaves of the existing allowed-IP source factors. These contracts
preserve an observation of actual calls; they do not replace those calls. -/
structure Contracts {V : Type} (view : WGWorld → V) : Prop where
  aip : ∀ {α : Type} (a : AipM α), SameView view (liftAip a)
  deleteList : ∀ id, SameView view (listDel id)
  appendList : ∀ pid id, SameView view (listAddTail pid id)
  sequence : SameView view
    (modifyDev fun d=>{d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}})
  removeNode : ∀ id, SameView view (AllowedIps.removeNodeBody id)

macro "allowed_frame_step " contract:term " at " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from AipM
     exact (($contract).aip _).wp (fun s=>s=$initial))
  | (rx_retention_head liftAip; exact (($contract).aip _).wp (fun s=>s=$initial))
  | (rx_retention_head listDel; exact (($contract).deleteList _).wp (fun s=>s=$initial))
  | (rx_retention_head listAddTail; exact (($contract).appendList _ _).wp (fun s=>s=$initial))
  | (rx_retention_head modifyDev; exact ($contract).sequence.wp (fun s=>s=$initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | rx_retention_step)

theorem placed {V : Type} {view : WGWorld → V} (contracts : Contracts view)
    (root : Slot) (bits key cidr : Nat) (pid : PeerId) (placed : Option NodeId) (exact : Bool) :
    SameView view (Config.addPlacedSource root bits key cidr pid placed exact) := by
  intro initial
  change Preserves (fun w=>view w=initial) _
  unfold Config.addPlacedSource
  repeat' allowed_frame_step contracts at initial

theorem root {V : Type} {view : WGWorld → V} (contracts : Contracts view)
    (root : Slot) (bits key cidr : Nat) (pid : PeerId) (trie : Option NodeId) :
    SameView view (Config.addRootSource root bits key cidr pid trie) := by
  intro initial
  change Preserves (fun w=>view w=initial) _
  unfold Config.addRootSource
  repeat' first
    | (rx_retention_head Config.addPlacedSource;
       exact (placed contracts _ _ _ _ _ _ _).wp (fun s=>s=initial))
    | allowed_frame_step contracts at initial

theorem add {V : Type} {view : WGWorld → V} (contracts : Contracts view)
    (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView view (WG.add root bits key cidr peer) := by
  rw [Config.add_transfer_source]
  intro initial
  change Preserves (fun w=>view w=initial) _
  repeat' first
    | (rx_retention_head Config.addRootSource;
       exact (AllowedFrame.root contracts _ _ _ _ _ _).wp (fun s=>s=initial))
    | allowed_frame_step contracts at initial

theorem insert {V : Type} {view : WGWorld → V} (contracts : Contracts view)
    (family addr cidr : Nat) (pid : PeerId) :
    SameView view (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w=>view w=initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head WG.add;
       exact (AllowedFrame.add contracts _ _ _ _ _).wp (fun s=>s=initial))
    | allowed_frame_step contracts at initial

theorem allowed {V : Type} {view : WGWorld → V} (contracts : Contracts view)
    (pid : PeerId) (ip : AllowedIpAttrs) : SameView view (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w=>view w=initial) _
  unfold setAllowedip WG.andM WG.orM
  repeat' first
    | (rx_retention_head WG.insert;
       exact (insert contracts _ _ _ _).wp (fun s=>s=initial))
    | allowed_frame_step contracts at initial

theorem remove {V : Type} {view : WGWorld → V} (contracts : Contracts view)
    (pid : PeerId) : SameView view (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep
  have read : SameView view (getPeer pid) := fun initial=>
    hoare_consequence (getPeer_spec pid (fun w=>view w=initial)) (fun _ h=>h)
      (fun _ _ h=>h.1)
  have ambient {α : Type} (a : AmbientM α) : SameView view (StateT.lift a : WG.M α) :=
    fun initial=>hoare_liftAmbient a (fun w=>view w=initial)
  apply read.bind
  intro p
  apply (ambient (AmbientM.branch .removeListEmpty p.allowedipsList.isEmpty)).bind
  intro empty
  cases empty with
  | true => exact SameView.pure view ()
  | false =>
    apply contracts.sequence.bind
    intro _
    apply (DumpComposition.forIn_sameView p.allowedipsList ()
      (fun id _=>AllowedIps.removeStep id) (fun id _=>?_)).bind
    · intro _
      exact ambient (AmbientM.branch .removeListIter false)
    · unfold AllowedIps.removeStep
      exact (ambient (AmbientM.branch .removeListIter true)).bind (fun _=>
          (contracts.deleteList id).bind (fun _=>contracts.removeNode id))
end Leanux.Proofs.WG.Config.AllowedFrame
