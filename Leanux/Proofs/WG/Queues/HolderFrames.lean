import Leanux.Proofs.WG.Queues.HolderCallbacks

/-! A holder frame keeps every actual surviving TX queue and the other
holder fields. Peer erasure is allowed; funding separately forbids a remaining
charged owner from silently disappearing. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

structure Frame (w v : WGWorld) : Prop where
  passive : passiveView v = passiveView w
  send : sendView v = sendView w
  tx : ∀ pid batches, handoffTxView v pid = some batches → handoffTxView w pid = some batches

theorem Frame.refl (w : WGWorld) : Frame w w := ⟨rfl,rfl,fun _ _ h => h⟩

theorem Frame.trans (first : Frame w u) (next : Frame u v) : Frame w v :=
  ⟨next.passive.trans first.passive,next.send.trans first.send,
    fun pid batches present => first.tx pid batches (next.tx pid batches present)⟩

theorem Frame.of_store (same : wgStoreView v = wgStoreView w) : Frame w v := by
  have dev : v.dev = w.dev := congrArg WGStoreView.dev same
  have sock7 : v.nlSock7 = w.nlSock7 := congrArg WGStoreView.nlSock7 same
  have sock8 : v.nlSock8 = w.nlSock8 := congrArg WGStoreView.nlSock8 same
  refine ⟨?_,?_,?_⟩
  · simp only [passiveView,dev,sock7,sock8]
  · simp only [sendView,dev]
  · intro pid batches present
    simpa only [handoffTxView,dev] using present

theorem Aligned.frame {holders : DurableHolders} (hi : holders.Aligned w)
    (frame : Frame w v) : holders.Aligned v := by
  have list := congrArg Prod.fst frame.passive
  have clear := congrArg (fun x => x.2.1) frame.passive
  have cursor7 := congrArg (fun x => x.2.2.1) frame.passive
  have cursor8 := congrArg (fun x => x.2.2.2) frame.passive
  refine ⟨hi.base.trans list.symm,?_,hi.clear.trans clear.symm,?_,
    hi.cursor7.trans cursor7.symm,hi.cursor8.trans cursor8.symm⟩
  · intro d hd
    have same := frame.send
    cases hw : w.dev with
    | none => simp [sendView,hd,hw] at same
    | some old =>
      have eq : d.sendWorkQueue = old.sendWorkQueue := by
        simpa only [sendView,hd,hw,Option.map_some,Option.some.injEq] using same
      exact eq.trans (hi.send old hw)
  · intro pid batches found
    exact hi.tx pid batches (frame.tx pid batches found)

/-- Enrich any existing phase contract with the current complete holder
account. The carrier predicate still charges holders and transient loans once. -/
def Accounted (P : Reservations → List RxJoint.Event → World → Prop)
    (loans : Reservations) (history : List RxJoint.Event) (w : World) : Prop :=
  ∃ holders : DurableHolders, holders.Aligned w.wg ∧ P (holders.owners ++ loans) history w

/-- An unchanged-holder phase rule reuses its existing source proof. The
observer's own erasure supplies the exact normal execution used by the frame. -/
theorem accounted_rule {α β : Type}
    {P : Reservations → List RxJoint.Event → World → Prop}
    {Q : Reservations → α → List RxJoint.Event → World → Prop}
    (action : RxJoint.Obs α) (original : Leanux.M β) (project : α → β)
    (appends : Appends action) (erases : ErasesTo project action original)
    (old : ∀ loans, PrefixEnsures (P loans) (fun _ => True) action (Q loans))
    (frame : ∀ w x v, original.run w = .ok (x,v) → Frame w.wg v.wg)
    (loans : Reservations) :
    PrefixEnsures (Accounted P loans) (fun _ => True) action
      (fun x => Accounted (fun owners => Q owners x) loans) := by
  apply PollCarrier.normal_spec appends
  intro w h x v hi run
  obtain ⟨holders,aligned,phase⟩ := hi
  have post := (old (holders.owners ++ loans) w h phase).choose_spec.2.2
  rw [run] at post
  have native : original.run w = .ok (project x,v) := by rw [←erases w h,run]; rfl
  exact ⟨holders,aligned.frame (frame w (project x) v native),post⟩

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
