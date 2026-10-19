import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCarrierReceive
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionEncryptionFrames

/-! Existing encryption and ring observers retain their exact histories;
native erasure and an independent no-socket-event frame are both required. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

private theorem old_native (body : PrefixM Journal.Event α) (native : Leanux.M α)
    (erases : ErasesPrefix body native) (appends : Appends body)
    (quiet : HistoryFrame oldSocket? body) (frame : SameView EmissionOuter.Sent native) :
    ProductSafe (product body) := by
  intro w h hi
  obtain ⟨suffix,grown⟩ := Appends.focus Event.old old? body w h
  refine ⟨suffix,grown,True.intro,?_⟩
  cases run : (runPrefix (product body) w h).1 with
  | error _ => trivial
  | ok result =>
    have nativeRun := (focusPrefix_erases Event.old old? erases w h).symm.trans run
    have sent := (ProjectedAction.iff_run _ _ _).mp frame w result.1 result.2 nativeRun
    obtain ⟨earlier,kept⟩ := hi
    refine ⟨earlier,?_⟩
    change emitted (runPrefix (focusPrefix Event.old old? body) w h).2 = earlier ++ EmissionOuter.Sent result.2
    rw [old_history_quiet body appends quiet,sent]
    exact kept

theorem poll : ProductSafe hooks.poll := by
  apply old_native Journal.poll (liftWG TxRing.pollSource)
  · intro w h
    have projected := congrArg Prod.fst (Journal.poll_projects w h)
    have maps : (fun x : Option (List SkbId) × World => (id x.1,x.2)) = id := by funext ⟨value,v⟩; rfl
    rw [maps,Except.map_id] at projected
    exact projected.symm
  · exact (Appends.focus _ _ _).receiptObserved
  · exact HistoryFrame.receiptObserved
      (fun w h => focusPrefix_other _ _ oldSocket? (fun _ => rfl) _ w h) (fun _ => rfl)
  · exact EmissionOuter.wg _ EmissionFrames.ring_poll

theorem encrypt (item : Option (List SkbId)) : ProductSafe (hooks.encrypt item) := by
  apply product_native_callback (RxWorkers.encryptStepTailSource item)
  · exact CallbackQuiet.encrypt contributing? (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) item
  · apply CallbackFrames.product_erases old? (CausalJournal.encrypt_projects item)
    intro w h
    have projected := congrArg Prod.fst (Journal.encrypt_projects item w h)
    have maps : (fun x : Bool × World => (id x.1,x.2)) = id := by funext ⟨value,v⟩; rfl
    rw [maps,Except.map_id] at projected
    exact projected.symm
  · exact EmissionFrames.encrypt_tail item

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
