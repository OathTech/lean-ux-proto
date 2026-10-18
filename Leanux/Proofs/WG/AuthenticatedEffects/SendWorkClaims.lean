import Leanux.Proofs.WG.AuthenticatedEffects.SendWorkFrames

/-! A dispatch keeps the exact selected queue ticket through its native worker
suffix, including a later Stop. The live queue carrier remains an explicit
caller obligation until the complete initialized driver transports it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem dispatch_native_suffix (w : World) (r : RunWitness PeerId)
    (reached : r ∈ (runPrefix dispatch w []).2) :
    (runPrefix dispatch w []).1 = (Leanux.liftWG (runFlushedSendWork r.value)).run r.after := by
  simp only [dispatch,runPrefix_bind,runPrefix_captureRun] at reached ⊢
  cases run : select.run w with
  | error e => simp [run] at reached
  | ok out =>
    rcases out with ⟨pid,v⟩
    simp only [run,runPrefix_emit,runPrefix_lift,List.nil_append,List.mem_singleton] at reached
    subst r
    simp only [runPrefix_emit,runPrefix_lift]

theorem dispatch_completed (w v : World) (carrier : Carrier h tickets w.wg)
    (r : RunWitness PeerId) (reached : r ∈ (runPrefix dispatch w []).2)
    (run : (runPrefix dispatch w []).1 = .ok ((),v)) :
    ∃ ticket rest, Selected tickets r.value ticket rest ∧ ticket.Valid h ∧ Carrier h rest v.wg := by
  have receipt := dispatch_receipts w r reached
  obtain ⟨ticket,rest,selected⟩ := select_exists tickets r.value (carrier.1 ▸ receipt.2.2.2)
  have suffixRun := (dispatch_native_suffix w r reached).symm.trans run
  rw [liftWG_run] at suffixRun
  cases native : ((runFlushedSendWork r.value).run r.after.wg).run r.after.ambient with
  | error e => simp [native,Except.map] at suffixRun
  | ok out =>
    rcases out with ⟨⟨result,afterWG⟩,afterAmbient⟩
    cases result
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq,true_and] at suffixRun
    subst v
    have input : Carrier h tickets r.after.wg := by simpa only [receipt.2.2.1] using carrier
    exact ⟨ticket,rest,selected,flushed_transports r.value _ _ _ _ input selected native⟩

theorem ticket_authenticated (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (ticket : Ticket)
    (valid : ticket.Valid (runWGPrefix (WorkRoot.receive msg src) w a []).2) :
    ∃ pre post,
      (runWGPrefix (WorkRoot.receive msg src) w a []).2 = pre ++ .queued ticket.receipt :: post ∧
      pre.length = ticket.index ∧
      WorkRoot.AuthenticatedAt pre ticket.receipt.origin ticket.receipt.kind ticket.peer := by
  obtain ⟨pre,post,position,index⟩ := valid.position
  exact ⟨pre,post,position,index,
    (WorkRoot.queued_authenticated msg src w a pre post ticket.receipt position).2⟩

theorem dispatch_authenticated (msg : Key) (src : SkbSource) (before : WGWorld) (ambient : Ambient)
    (w : World) (tickets : List Ticket)
    (carrier : Carrier (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 tickets w.wg)
    (r : RunWitness PeerId) (reached : r ∈ (runPrefix dispatch w []).2) :
    ∃ ticket rest pre post,
      Selected tickets r.value ticket rest ∧ ticket.peer = r.value ∧
      (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 = pre ++ .queued ticket.receipt :: post ∧
      pre.length = ticket.index ∧
      WorkRoot.AuthenticatedAt pre ticket.receipt.origin ticket.receipt.kind ticket.peer := by
  obtain ⟨ticket,rest,selected,valid,_⟩ := dispatch_ticket w carrier r reached
  obtain ⟨pre,post,position,index,cause⟩ := ticket_authenticated msg src before ambient ticket valid
  have peer : ticket.peer = r.value := by
    obtain ⟨_,_,_,_,same,_⟩ := selected
    exact same
  exact ⟨ticket,rest,pre,post,selected,peer,position,index,cause⟩

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
