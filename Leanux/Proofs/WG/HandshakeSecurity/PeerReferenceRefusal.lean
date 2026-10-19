import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.RefusalPositivePeers

/-! Initialized response refusal preserves complete resident peer records.
Native successful-loan repayment and failed-lookup positivity compose at the
same actual final-journal receipt, without a reachability or funding premise. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem refusal_positive {w : WGWorld} (positive : Inv w) :
    AuthenticatedEffects.ResponseLoan.Positive w := by
  intro pid peer found
  apply positive pid peer.refcount
  change ((w.dev.bind fun d => d.peers[pid]?).map Peer.refcount) = some peer.refcount
  exact congrArg (Option.map Peer.refcount) found

/-- The actual cookie callback's completed native witness retains its positive
entry condition and the refusal frame. The entry carrier is explicit here;
no initialized occurrence is inferred from an omitted journal event. -/
theorem cookie_callback_entry (msg : Key) :
    StatePrefixEnsures (fun h w _ => StateInv (E := Exchange.Event) h w) Safe (captureWGRun (cookieMessageConsume msg))
      (fun r h w _ => StateInv (E := Exchange.Event) h w ∧ r.Valid (cookieMessageConsume msg) ∧
        AuthenticatedEffects.ResponseLoan.Positive r.before ∧
        ((runWGPrefix (AuthenticatedEffects.acceptedCookie msg) r.before r.ambientBefore []).2 = [] →
          AuthenticatedEffects.ResponseLoan.residents r.after =
            AuthenticatedEffects.ResponseLoan.residents r.before)) := by
  apply StatePrefixEnsures.captureWGRun _ (fun _ _ _ before => before.1)
  intro h w a value v b before run
  have positive := refusal_positive before.2
  refine ⟨⟨before.1,?_⟩,run,positive,?_⟩
  · exact (Framing.hoare_iff_run_ambient _ _ _).mp (cookie_consume msg) w a value v b before.2 run
  · intro unaccepted
    cases value
    exact AuthenticatedEffects.ResponseLoan.cookie_refusal msg w v a b positive unaccepted run


theorem final_response_refusal (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List AuthenticatedEffects.CausalJournal.Event) (msg : Key)
    (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2 =
      pre ++ AuthenticatedEffects.CausalJournal.Event.exchange (.consumeResponse msg r) :: post)
    (refused : r.value = none) :
    AuthenticatedEffects.ResponseLoan.residents r.after = AuthenticatedEffects.ResponseLoan.residents r.before := by
  obtain ⟨positive,valid⟩ := final_response_entry trace placeholders pre post msg r position
  apply AuthenticatedEffects.ResponseLoan.response_refusal msg r.before r.after
    r.ambientBefore r.ambientAfter (refusal_positive positive)
  simpa only [WGRunWitness.Valid,refused] using valid

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
