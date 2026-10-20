import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxAccountingAccessSource

/-! The actual peer getter funds the byte counter write. Every native access
cut keeps the same packet ledger and already-established terminal outcome. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxAccountingAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points CompleteCarrier

theorem canonical_framed (pid : PeerId) (size : Nat) (h : List LifetimeEvent) : Framed (canonical pid size) w a h := by
  refine ⟨True.intro,?_⟩
  intro p v b middle read
  have native : (getPeer pid).run w a=.ok ((p,v),b) :=
    (getPeerMixed_erases pid w a h).symm.trans (congrArg Prod.fst read)
  obtain ⟨rfl,rfl,d,device,resident⟩:=read_peer_resident native
  exact ⟨d,p,device,resident,rfl,rfl,rfl⟩

/-- Security: native byte-counter writes preserve the same selected packet
owners and terminal records even before their lifetime access receipt. -/
theorem RootPoint.accounted (before : Accounted h ledger debts locals w.wg)
    (point : RootPoint pid size w h u middle) : Accounted middle ledger debts locals u.wg := by
  cases point with
  | source point=>
      obtain ⟨suffix,extended⟩:=point.appends
      rw [extended,List.drop_left]
      apply (before.same_view (point.view (canonical_framed pid size _))).append_quiet
      · intro event member
        obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
        exact (KeyAccess.encode_quiet source).1
      · intro event member
        obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
        exact (KeyAccess.encode_quiet source).2

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxAccountingAccess
