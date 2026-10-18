import Leanux.Proofs.WG.HandshakeSecurity.ResponderConfigurationFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining

theorem aip_native (a : AipM α) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (liftAip a) := by
  apply hoare_liftAip
  intro w d store hi hd
  refine ⟨hi.1.frame ?_, CurrentSlots.fields_transport hi.2 ?_⟩
  · unfold current; rw [hd]; rfl
  · unfold CurrentSlots.fields RxCredits.keyWords
    simp only [hd, Option.map_some, Option.bind_some]

macro "responder_aip_step " confirmed:term : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip_native _ $confirmed)
  | (rx_retention_head liftAip; exact aip_native _ $confirmed)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | responder_handshake_step $confirmed)

theorem listAdd_native (pid : PeerId) (id : NodeId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (listAddTail pid id) := by
  unfold listAddTail
  exact peerUpdate_native pid (fun p => {p with allowedipsList := p.allowedipsList ++ [id]}) (fun _ => rfl) confirmed

theorem listDel_native (id : NodeId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (listDel id) :=
  native_fields (pool_of_material (listDel_material id))
    (CurrentSlots.Removal.listDel_fields id) confirmed

theorem addAip_native (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch, branchCmp, invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact listAdd_native _ _ confirmed)
    | (rx_retention_head listDel; exact listDel_native _ confirmed)
    | responder_aip_step confirmed

theorem insertAip_native (family addr cidr : Nat) (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact addAip_native _ _ _ _ _ confirmed)
    | responder_aip_step confirmed

theorem allowedip_native (pid : PeerId) (ip : AllowedIpAttrs) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact insertAip_native _ _ _ _ confirmed)
    | responder_aip_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
