import Leanux.Proofs.WG.RetirementSecurity.TxWorkActors
import Leanux.Proofs.WG.Queues.TxDispatchCuts

/-! Scheduler record reads preserve the actual suspended-activation list.
Unlike a product-store frame, these facts retain the Ambient component used
to account for outstanding TX actors. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxActorFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Std.Do

theorem skip : SameView Ambient.suspended AmbientM.skipAmbient := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases hidden:w.hidden <;> simp [AmbientM.skipAmbient,hidden] at run <;> rcases run with ⟨rfl,rfl⟩ <;> rfl

theorem note (site : Nat) : SameView Ambient.suspended (AmbientM.noteNetRxStart site) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.noteNetRxStart at run
  split at run <;> cases run <;> rfl

theorem hidden (site : HiddenSite) : SameView Ambient.suspended (AmbientM.hidden site) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.hidden at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨_,u,skipped,run⟩:=run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨_,t,noted,run⟩:=run
  have first := (ProjectedAction.iff_run _ _ _).mp skip w () u skipped
  have second := (ProjectedAction.iff_run _ _ _).mp (note site.info.id) u () t noted
  have tail : v.suspended=t.suspended := by
    simp only [MaterialOrigin.bind_ok] at run
    obtain ⟨saved,z,read,run⟩:=run
    cases read
    split at run
    all_goals repeat' first | (change Except.error _ = Except.ok _ at run; cases run) | split at run | (rw [MaterialOrigin.bind_ok] at run; obtain ⟨x,y,step,run⟩:=run; cases step) | (cases run; rfl)
  exact tail.trans (second.trans first)

theorem lift_ambient {action : AmbientM α} (frame : SameView Ambient.suspended action) :
    SameView (fun w : World=>(w.wg,w.ambient.suspended)) (liftAmbient action) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  rw [liftAmbient_run] at run
  cases native:action.run w.ambient with
  | error stop=>simp [native,Except.map] at run
  | ok output=>
    obtain ⟨value,b⟩:=output
    simp only [native,Except.map,Except.ok.injEq] at run
    cases run
    exact Prod.ext rfl ((ProjectedAction.iff_run _ _ _).mp frame w.ambient result b native)

theorem hidden_product (site : HiddenSite) :
    SameView (fun w : World=>(w.wg,w.ambient.suspended)) (Leanux.hidden site : Leanux.M (List UInt8)) :=
  lift_ambient (hidden site)

theorem peek_unit (worker : Worker) : SameView Ambient.suspended (AmbientM.peekUnit worker) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.peekUnit at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨_,u,skipped,tail⟩:=run
  have same:= (ProjectedAction.iff_run _ _ _).mp skip w () u skipped
  rw [MaterialOrigin.bind_ok] at tail
  obtain ⟨saved,t,read,tail⟩:=tail
  cases read
  split at tail
  all_goals repeat' first | split at tail | (cases tail; exact same)

theorem resolve (worker : Worker) (unit : Nat) (queue : List Nat) :
    SameView Ambient.suspended (AmbientM.resolveUnit worker unit queue) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.resolveUnit at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  split at tail
  all_goals repeat' first
    | (change Except.error _ = Except.ok _ at tail; cases tail)
    | split at tail
    | (rw [MaterialOrigin.bind_ok] at tail; obtain ⟨x,y,step,tail⟩:=tail; cases step)
    | (cases tail; rfl)

theorem peek_site : SameView Ambient.suspended AmbientM.peekHiddenSite := by
  unfold AmbientM.peekHiddenSite
  apply skip.bind
  intro _
  apply (show SameView Ambient.suspended (get : AmbientM Ambient) from by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w result v run
    cases run
    rfl).bind
  intro _
  exact SameView.pure _ _

theorem budget : SameView Ambient.suspended AmbientM.recordBudget := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.recordBudget at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  split at tail <;> cases tail <;> rfl

theorem native_read {action : WG.M α}
    (read : ∀w a result v b,((action.run w).run a)=.ok ((result,v),b)→v=w ∧ b=a) :
    SameView id (liftWG action) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  rw [liftWG_run] at run
  cases native:(action.run w.wg).run w.ambient with
  | error stop=>simp [native,Except.map] at run
  | ok output=>
    obtain ⟨⟨value,g⟩,b⟩:=output
    simp only [native,Except.map,Except.ok.injEq] at run
    cases run
    obtain ⟨rfl,rfl⟩:=read w.wg w.ambient result g b native
    rfl

theorem device : SameView id (liftWG getDev) :=
  native_read (fun _ a _ _ b run=>
    ⟨(RxCredits.DecryptCarrier.getDev_current a b run).1,(RxCredits.DecryptCarrier.getDev_current a b run).2.1⟩)

theorem peer (pid : PeerId) : SameView id (liftWG (getPeer pid)) :=
  native_read (fun w a p v b run=>
    ⟨(Origins.getPeer_return pid w v p a b run).1,(Origins.getPeer_return pid w v p a b run).2.1⟩)

theorem occupancy (act : Activation) : SameView id (Env.Activation.occupancy act) := by
  intro initial
  have stopped {α : Type} (message : String) : Preserves (fun w : World=>w=initial)
      (Leanux.invariant message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  have dev : Preserves (fun w : World=>w=initial) (monadLift getDev : Leanux.M Device) := device initial
  have readPeer (pid : PeerId) : Preserves (fun w : World=>w=initial) (monadLift (getPeer pid) : Leanux.M Peer) := peer pid initial
  change Preserves (fun w : World=>w=initial) _
  routing_tx_source [Env.Activation.occupancy] using [dev,readPeer,stopped]

theorem packet (skb : SkbId) : SameView id (liftWG (getTxSkb skb)) :=
  native_read (fun w a p v b run=>
    ⟨(Packets.getTxSkb_current skb w v p a b run).1,(Packets.getTxSkb_current skb w v p a b run).2.1⟩)

theorem has_work (act : Activation) : SameView id (Env.Activation.hasWork act) := by
  intro initial
  have stopped {α : Type} (message : String) : Preserves (fun w : World=>w=initial)
      (Leanux.invariant message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  have dev : Preserves (fun w : World=>w=initial) (monadLift getDev : Leanux.M Device) := device initial
  have readPeer (pid : PeerId) : Preserves (fun w : World=>w=initial) (monadLift (getPeer pid) : Leanux.M Peer) := peer pid initial
  have readPacket (skb : SkbId) : Preserves (fun w : World=>w=initial) (monadLift (getTxSkb skb) : Leanux.M DataPacket) := packet skb initial
  change Preserves (fun w : World=>w=initial) _
  routing_tx_source [Env.Activation.hasWork] using [dev,readPeer,readPacket,stopped]

theorem consistent (act : Activation) : SameView id (Env.Activation.consistent act) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold Env.Activation.consistent at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  split at tail
  all_goals first | (cases tail; rfl) | (change Except.error _ = Except.ok _ at tail; cases tail)

end Leanux.Proofs.WG.RetirementSecurity.TxActorFrames
