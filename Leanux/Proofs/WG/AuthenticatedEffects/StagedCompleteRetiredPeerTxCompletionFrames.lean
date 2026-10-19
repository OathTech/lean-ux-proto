import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxFrames

/-! Completion acquires its actual send-work delta; the subsequent batch
payment consumes the selected loan and retains that same delta. These
contracts describe successful native returns, not a state after Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders RetirementSecurity

theorem Account.tx_complete (account : Account holders carriers loans w)
    (pid : PeerId) (item : List SkbId) (a b : Ambient)
    (run : ((createDataDone pid item).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ delta.tx = [] ∧
      Account (holders.absorb delta) carriers loans v := by
  obtain ⟨delta,step,noTx,funded,stable⟩ := TxReservation.createDataDone_handoff
    pid item ⟨account.funded.carriers,account.stable⟩ a b run
  have passive := (ProjectedAction.iff_run_ambient _ _ _).mp
    (createDataDone_passive pid item) w a () v b run
  have start : Account holders carriers (loans ++ []) w := by simpa using account
  exact ⟨delta,step,noTx,by simpa using start.handoff step funded.keys passive stable⟩

theorem Account.tx_complete_dispose
    (account : Account holders carriers (owner :: loans) w)
    (item : List SkbId) (key : KeypairId) (a b : Ambient)
    (run : (((do createDataDone owner.slot item
                 TxDisposition.disposeSource owner.slot item key) : WG.M Bool).run w).run a =
      .ok ((result,v),b)) :
    result = true ∧ ∃ middle ambient delta,
      ((createDataDone owner.slot item).run w).run a = .ok (((),middle),ambient) ∧
      Handoff w middle [] [] delta ∧ delta.tx = [] ∧
      Account (holders.absorb delta) carriers loans v := by
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,middle,ambient,complete,dispose⟩ := run
  cases u
  obtain ⟨delta,step,noTx,completed⟩ := account.tx_complete owner.slot item a ambient complete
  obtain ⟨result,paid⟩ := completed.tx_dispose item key ambient b dispose
  exact ⟨result,middle,ambient,delta,complete,step,noTx,paid⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
