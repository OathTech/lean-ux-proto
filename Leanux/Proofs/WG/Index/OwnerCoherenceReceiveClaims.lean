import Leanux.Proofs.WG.Index.DataIngressRulesSource
import Leanux.Proofs.WG.Index.DataIngressReferenceFrames
import Leanux.Proofs.WG.Index.DataIngressAcquireSource
import Leanux.Proofs.WG.Index.OwnerReferenceFrames
import Leanux.Proofs.WG.Index.RxQueueOwnerFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceLookupHeldClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairReleaseClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

open Leanux.Proofs.Framing Lifetimes Queues DataIngress in
/-- Actual normal data ingress preserves resident hashed-owner coherence. The
lookup and key acquisition supply the held references used by cleanup; the
entry contract adds no reference bound, readiness or alias restriction. -/
theorem consumeData_owner_coherent (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Campaign2.Ensures (consumeData msg src ds) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  let safe := DeviceSafe HashedOwnersCoherent
  change Ensures (consumeData msg src ds) safe (fun _=>safe)
  refine (Noise.ensures_iff (consumeData msg src ds) safe (fun _=>safe)).mpr ?_
  have putKey (kid pid : Nat) : Hoare (keypairPut (some kid) false) (Held safe kid pid)
      (fun _=>Credit safe (some pid)) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    obtain ⟨initial,d,p,k,device,resident,peerCount,key,keyCount⟩ := pre
    have after := keypairPut_owner_coherent (some kid) false w a result v b initial run
    obtain ⟨out,ending,tail,actual,effect⟩ := Config.keypairPut_retained kid d k key keyCount w a device
    rw [run] at actual
    cases actual
    refine ⟨after,?_⟩
    intro selected equal
    cases equal
    exact ⟨Config.withKeypair d kid {k with refcount:=k.refcount-1},p,effect,resident,peerCount⟩
  have putPeer (peer : Option PeerId) : Hoare (peerPut peer) (Credit safe peer) (fun _=>safe) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    cases peer with
    | none => cases run; exact pre.1
    | some pid =>
      obtain ⟨d,p,device,resident,count⟩ := pre.2 pid rfl
      exact peerPut_owner_coherent pid d p resident (by omega) (by intro eq; omega)
        w a result v b ⟨device,pre.1⟩ run
  have frontRule := positive_front HashedOwnersCoherent msg keypairAcquire_owner_coherent
    ((ensures_iff _ _ _).mp (indexLookup_keypair_held (u32le msg 4)))
  apply DataIngressRules.preserves safe (Held safe) (Credit safe) msg src ds frontRule
    (fun _ _ _ h=>h.1) putKey putPeer
  · intro kid pid
    exact held_frame_at safe _ (coherent_frame _ (fun d=>hoare_liftSkb_references_variant _ d))
      (fun d=>hoare_liftSkb_references_variant _ d) kid pid
  · intro kid pid id
    exact held_frame_at safe _ (coherent_frame _ (fun d=>enqueuePerDeviceAndPeerRx_spec_references_variant id d))
      (fun d=>enqueuePerDeviceAndPeerRx_spec_references_variant id d) kid pid
  · intro kid pid id
    exact held_frame_at safe _ (coherent_frame _ (fun d=>enqueuePerPeerRx_pure_spec_references_variant id .dead d))
      (fun d=>enqueuePerPeerRx_pure_spec_references_variant id .dead d) kid pid
  · intro id
    exact skb_coherent _

end Leanux.Proofs.WG.Index
