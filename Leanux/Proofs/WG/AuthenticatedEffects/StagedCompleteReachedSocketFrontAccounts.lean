import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketFrontPoints

/-! Routing and cache cuts carry the same packet account. Only the later
native datagram append and socket receipt use the pending-settlement carrier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketFront
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier

/-- Security: every declared native socket-front point retains the same
packet owner and terminal ledger before the original datagram append. -/
theorem RootPoint.accounted (before : Accounted h ledger debts locals w.wg)
    (point : RootPoint pid packet peer ipv4 w h u middle) : Accounted middle ledger debts locals u.wg := by
  cases point with
  | source point=>
      obtain ⟨suffix,extended⟩:=point.appends
      rw [extended,List.drop_left]
      apply (before.same_view (point.view (canonical_framed _ _ _ _ _ _ _))).append_quiet
      · intro event member
        obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
        exact (KeyAccess.encode_quiet source).1
      · intro event member
        obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
        exact (KeyAccess.encode_quiet source).2

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketFront
