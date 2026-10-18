import Leanux.Proofs.WG.Index.RetirementBulkSource
import Leanux.Proofs.WG.Index.RetirementRetentionEffects
import Leanux.Proofs.WG.Origins.ConfiguredRemoval

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- Only trie nodes and allowed-IP peer lists are hidden by the landed free
effect. The actual normal clear retains every prior dead-owner reservation. -/
theorem free_deadHashedReserved (retired : Reservations) :
    Preserves (fun w : WGWorld => ∀ d, w.dev = some d → DeadHashedReserved retired d)
      WG.free := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b reserved run
  have effect := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (wgStoreView w)) w a result v b rfl run
  have mask := congrArg (fun x : WGStoreView × (PeerId → Option Peer) => x.1.dev) effect
  intro final out
  cases device : w.dev with
  | none =>
    simp [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,wgStoreView,
      out,device] at mask
  | some d =>
    have fields : {final with nodes := {}, peers := {}} =
        {AllowedIps.resetAllowedips d with nodes := {}, peers := {}} := by
      simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,wgStoreView,
        out,device,Option.map_some,Option.some.injEq] using mask
    have epoch := congrArg Device.ifindex fields
    have table := congrArg Device.indexTable fields
    have keys := congrArg Device.keypairs fields
    refine deadHashedReserved_transport retired d final epoch
      (fun entry member => table ▸ member) ?_ ?_ (reserved d device)
    · intro entry _ kid owner
      simp only [owner,ownerWord]
      rw [keys]
      rfl
    · intro pid p found
      have cell := congrFun (congrArg Prod.snd effect) pid
      simp only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,wgStoreView,
        out,device,Option.map_some,Option.bind_some,AllowedIps.resetAllowedips,
        found] at cell
      cases oldFound : d.peers[pid]? with
      | none => simp [oldFound] at cell
      | some old =>
        have eq : {p with allowedipsList := []} = {old with allowedipsList := []} := by
          simpa only [oldFound,Option.map_some,Option.some.injEq] using cell
        exact ⟨old,rfl,(congrArg Peer.internalId eq).symm,
          (congrArg Peer.isDead eq).symm⟩

end Leanux.Proofs.WG.Index
