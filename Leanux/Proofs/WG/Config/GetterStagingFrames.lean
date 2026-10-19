import Leanux.Proofs.WG.Config.GetterCleanupWorkerFrames
import Leanux.Proofs.WG.Index.StagingPreservationSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterStaging
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open GetterCleanup

theorem skb {α : Type} (action : SkbM α) :
    SameView getterMetadata (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro g d store pre hd
  simpa only [getterMetadata,hd,Option.map_some,sendConfiguration] using pre

theorem acquire_peer (pid : PeerId) : SameView getterMetadata (peerGet pid) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold peerGet
  repeat' first
    | (rx_retention_head refcountInc; unfold refcountInc)
    | getter_cleanup_step initial

theorem acquire_key (kid : Option KeypairId) : SameView getterMetadata (keypairGet kid) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold keypairGet
  repeat' first
    | (rx_retention_head refcountIncNotZero; unfold refcountIncNotZero)
    | getter_cleanup_step initial

theorem cpu (pid : PeerId) : SameView getterMetadata (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold cpumaskChooseOnline
  simp only [Nat.mod_one,Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]
  simp only [map_eq_pure_bind]
  repeat' getter_cleanup_step initial

def contracts (initial : GetterMetadata) :
    Index.StagingPreservation.Contracts (fun g=>getterMetadata g=initial) where
  peer := fun _ _=>True
  key := fun _ _=>True
  readPeer := by
    intro pid α next Q body
    exact ensures_bind _ _ (normal_frame (read_peer pid) initial) (fun p=>body p trivial)
  readKey := by
    intro kid α next Q body
    exact ensures_bind _ _ (normal_frame (read_key kid) initial) (fun k=>body k trivial)
  setPeer := fun pid p _=>normal_frame (set_peer pid p) initial
  setKey := fun kid k _=>normal_frame (set_key kid k) initial
  modify := fun f _ _ _ header=>normal_frame (modify_device f header) initial
  peerGet := fun pid=>normal_frame (acquire_peer pid) initial
  peerPut := fun pid=>normal_frame (peerPut_metadata_getter_variant pid) initial
  keyGet := fun kid=>normal_frame (acquire_key kid) initial
  release := fun kid now=>normal_frame (keypairPut_rest_getter_variant kid now) initial
  skb := fun a=>normal_frame (skb a) initial
  cpu := fun pid=>normal_frame (cpu pid) initial


end Leanux.Proofs.WG.Config.GetterStaging
