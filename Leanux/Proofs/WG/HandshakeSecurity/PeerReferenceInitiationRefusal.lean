import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceRefusal

/-! The existing native initiation-refusal view includes all peer records and
the full keypair store. Project both at the same initialized consumer receipt. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AuthenticatedEffects

theorem final_initiation_refusal_records (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (msg : Key)
    (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ CausalJournal.Event.exchange (.consumeInitiation msg r) :: post)
    (refused : r.value = none) :
    ResponseLoan.residents r.after = ResponseLoan.residents r.before ∧
    ResponseLoan.residentKeys r.after = ResponseLoan.residentKeys r.before := by
  have valid := (final_entry trace placeholders pre post (.consumeInitiation msg r) position).2
  have native : ((consumeInitiation msg).run r.before).run r.ambientBefore =
      .ok ((none,r.after),r.ambientAfter) := by
    simpa only [Exchange.Event.Valid,WGRunWitness.Valid,refused] using valid
  have frame := initiation_refusal_restores_peers msg r.before r.after
    r.ambientBefore r.ambientAfter native
  refine ⟨congrArg Prod.snd frame,?_⟩
  funext kid
  have keys := congrArg (fun pair : WGStoreView × (PeerId → Option Peer) =>
    pair.1.dev.bind fun d => d.keypairs[kid]?) frame
  simpa only [PeerBorrow.view,PeerBorrow.outsidePeers,wgStoreView,ResponseLoan.residentKeys,
    Option.bind_map,Function.comp_def] using keys

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
