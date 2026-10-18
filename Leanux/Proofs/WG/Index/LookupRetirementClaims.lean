import Leanux.Proofs.WG.Index.LookupRetirementEffects
import Leanux.Proofs.WG.Index.IncomingIndexClaims
import Leanux.Proofs.WG.Index.LookupCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem indexLookup_retirement (retired : Reservations) (kinds : List IndexKind) (index : Nat) :
    Campaign2.Ensures (indexLookup kinds index)
      (fun s => View.OwnerCoherentSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.RetirementSafe retired s) := by
  intro g a result out b pre run final present
  cases device : g.dev with
  | none =>
    rw [indexLookup_factor] at run
    simp [lookupPrefix,liftIndex,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨actual,output,safe⟩ := indexLookup_preserves_coherent_source kinds index
      (DeadHashedReserved retired)
      (fun before pid p resident safe => peerWrite_deadHashedReserved retired before pid p _ resident rfl rfl safe)
      (writeSame_deadHashedReserved retired) d (pre.1 d device) (pre.2 d device)
      g a result out b device run
    rw [present] at output
    cases output
    exact safe

theorem indexLookup_indexCore_held (kinds : List IndexKind) (index : Nat) :
    Campaign2.Ensures (indexLookup kinds index) View.IndexCore
      (fun result s => View.IndexCore s ∧
        ∀ owner pid,result=some (owner,pid) → View.IndexCoreHeld pid s) := by
  intro g a result out b pre run
  have tables := (ensures_iff _ _ _).mpr (indexLookup_tables kinds index)
    g a result out b (fun d device => (pre d device).1) run
  have owners := indexLookup_peer_held kinds index g a result out b
    (fun d device => (pre d device).2.2.1) run
  have slots := indexLookup_hashSlots kinds index g a result out b
    ⟨fun d device => (pre d device).2.2.1,fun d device => (pre d device).2.1⟩ run
  have retired := indexLookup_retirement [] kinds index g a result out b
    ⟨fun d device => (pre d device).2.2.1,fun d device => (pre d device).2.2.2⟩ run
  have core : Reached.Core out := fun d device =>
    ⟨tables d device,slots.2 d device,owners.1 d device,retired d device⟩
  exact ⟨core,fun owner pid returned => ⟨core,owners.2 owner pid returned⟩⟩


end Leanux.Proofs.WG.Index
