import Leanux.Proofs.WG.Index.DataIngressRulesSource
import Leanux.Proofs.WG.Index.RxQueueFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

open Leanux.Proofs.Framing Lifetimes Queues in
/-- Every normal return of the actual data-ingress path preserves both index-table uniqueness properties and the keypair allocation bound. No ownership coherence, queue consistency, or readiness premise is required. -/
theorem consumeData_tables (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Campaign2.Ensures (consumeData msg src ds) View.TablesSafe (fun _ => View.TablesSafe) := by
  change Ensures (consumeData msg src ds) TablesSafeWG (fun _=>TablesSafeWG)
  refine (Noise.ensures_iff (consumeData msg src ds) TablesSafeWG (fun _=>TablesSafeWG)).mpr ?_
  have acquired (entry : Option (IndexOwner × PeerId)) :
      Preserves TablesSafeWG (Affiliation.receiveKeyAcquire entry) := by
    cases entry with
    | none =>
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b pre run
      simp [Affiliation.receiveKeyAcquire,keypairGetNull] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact pre
    | some pair =>
      rcases pair with ⟨owner,pid⟩
      cases owner with
      | handshake _ =>
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a result v b pre run
        cases run
      | keypair kid =>
        simp only [Affiliation.receiveKeyAcquire,pure_bind]
        exact preserves_bind (keypairGet_tables (some kid)) (fun _=>preserves_pure _)
  have frontRule : Hoare (do let entry←indexLookup [.keypair] (u32le msg 4); Affiliation.receiveKeyAcquire entry)
      TablesSafeWG (DataIngressRules.Acquired TablesSafeWG (fun _ _=>TablesSafeWG) (fun _=>TablesSafeWG)) := by
    apply hoare_consequence (preserves_bind (indexLookup_tables _ _) acquired)
    · exact fun _ h=>h
    · exact fun _ _ h=>⟨h,fun _=>h,fun _ _ _=>h⟩
  apply DataIngressRules.preserves TablesSafeWG (fun _ _=>TablesSafeWG) (fun _=>TablesSafeWG)
    msg src ds frontRule (fun _ _ _ h=>h) (fun kid _=>keypairPut_tables (some kid) false) peerPut_tables
  · intro kid pid
    exact (ensures_iff _ _ _).mp (liftSkb_tables (SkbStore.newRx _))
  · intro kid pid id
    exact (ensures_iff _ _ _).mp (enqueuePerDeviceAndPeerRx_spec_tables_variant id)
  · intro kid pid id
    exact (ensures_iff _ _ _).mp (enqueuePerPeerRx_pure_spec_tables_variant id .dead)
  · intro id
    exact (ensures_iff _ _ _).mp (liftSkb_tables (SkbStore.freeRx id))

end Leanux.Proofs.WG.Index
