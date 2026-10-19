import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingQueueNativeSource

/-! Packet-view frames for the literal queued decision and installation.
The cached setter is justified by its own native peer read. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive.QueueNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open CompleteCarrier TransmitSecurity
set_option maxHeartbeats 600000

theorem cached_write_view (fields : Fields f)
    (read : ((getPeer pid).run w).run a=.ok ((peer,u),c))
    (write : ((setPeer pid (f peer)).run u).run b=.ok (((),v),e)) :
    StagedEntry.view v=StagedEntry.view w := by
  have same : u=w := (Peers.getPeer_current pid w u peer a c read).1
  subst u
  cases device : w.dev with
  | none=>
    simp [getPeer,getDev,device,invariant,AmbientM.invariant] at read
    cases read
  | some d=>
    cases resident : d.peers[pid]? with
    | none=>
      simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at read
      cases read
    | some stored=>
      simp [getPeer,getDev,device,resident] at read
      obtain ⟨rfl,rfl⟩:=read
      simp [setPeer,modifyDev,device] at write
      rcases write with ⟨⟨rfl,rfl⟩,rfl⟩
      exact Queued.replace_peer device resident (fields stored).1 (fields stored).2.1 (fields stored).2.2

theorem update_view (fields : Fields f)
    (run : ((guardedUpdate pid f guardBody).run w).run a=.ok (((),v),b)) :
    StagedEntry.view v=StagedEntry.view w := by
  unfold guardedUpdate at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,read,tail⟩:=run
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨ignored,t,d,checked,write⟩:=tail
  cases ignored
  have same : t=u := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (guardBody peer) (fun state=>state=u)) u c () t d rfl checked
  subst t
  exact cached_write_view fields read write

theorem Shape.frame (shape : Shape action) : SameView StagedEntry.view action := by
  induction shape with
  | quiet source=>exact source.frame
  | update pid f guardBody fields=>
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    cases value
    exact update_view fields run
  | age site birth limit test=>exact (branchExpired_sameWGWorld site birth limit test).factor StagedEntry.view
  | bind head tail ihHead ihTail=>exact SameView.bind ihHead ihTail

theorem Point.view {action : WG.M α} {shape : Shape action}
    (point : Point shape w a v b rest) : StagedEntry.view v=StagedEntry.view w := by
  induction point with
  | entry=>rfl
  | returned shape run=>exact (ProjectedAction.iff_run_ambient _ _ _).mp shape.frame _ _ _ _ _ run
  | quiet source point=>exact point.view
  | reading fields point=>exact point.view
  | guarded fields read checked=>exact congrArg StagedEntry.view (Peers.getPeer_current _ _ _ _ _ _ read).1
  | left tail point ih=>exact ih
  | right head tail leading point ih=>
    exact ih.trans ((ProjectedAction.iff_run_ambient _ _ _).mp head.frame _ _ _ _ _ leading)

/-- Every fixed decision/install cut retains the same ledger and history;
neither the cached metadata write nor the borrow moves packet ownership. -/
theorem Point.accounted {action : WG.M α} {shape : Shape action}
    (point : Point shape w a v b rest) (before : Accounted h ledger debts locals w) :
    Accounted h ledger debts locals v := before.same_view point.view

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive.QueueNative
