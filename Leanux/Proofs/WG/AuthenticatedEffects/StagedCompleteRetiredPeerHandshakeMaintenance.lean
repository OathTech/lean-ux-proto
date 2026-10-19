import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeConsumers
import Leanux.Proofs.WG.Queues.HandshakeReception

/-! Native receive maintenance keeps the same reference account. Actual
staging absorbs exactly the delta chosen by the funded source theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

theorem fixed (action : WG.M α) (frame : ∀initial, Preserves (Frame initial) action)
    (keeps : ∀cs loans, Preserves (ClearWork.Inv cs loans) action)
    (peer : SameView peerView action) : Preserves (Account holders cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b account run
  have lower := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.fixed_rule)
      action frame keeps) w a x v b ⟨account.funded,account.stable⟩ run
  exact ⟨lower.1,account.upper.peer_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp peer w a x v b run),lower.2⟩

theorem control (action : WG.M α) (frame : ∀initial, Preserves (Frame initial) action)
    (same : SameView (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view) action) :
    Preserves (Account holders cs loans) action := by
  apply fixed action frame
  · intro cs loans
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.control_keeps) same
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a x v b run
    have eq := (ProjectedAction.iff_run_ambient _ _ _).mp same w a x v b run
    have carriers := ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) v).trans
      ((congrArg (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrierOf) eq).trans
        ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) w).symm)
    exact congrArg Prod.fst carriers

theorem mod_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (Account holders cs loans) (modPeerTimer site pid timer delay) :=
  control _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.mod_preserves) site pid timer delay)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.modPeerTimer_view) site pid timer delay)

theorem del_timer (pid : PeerId) (timer : PeerTimer) :
    Preserves (Account holders cs loans) (delTimer pid timer) :=
  control _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.del_preserves) pid timer)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.delTimer_view) pid timer)

theorem traversal (pid : PeerId) : Preserves (Account holders cs loans) (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp]
  repeat' first
    | (rx_retention_head modPeerTimer; exact mod_timer _ _ _ _)
    | (rx_retention_head Functor.discard
       apply discard_view_spec id (Account holders cs loans)
       change Preserves (Account holders cs loans) _
       exact mod_timer _ _ _ _)
    | (rx_retention_head getPeer; exact read _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem derived (pid : PeerId) : Preserves (Account holders cs loans) (timersSessionDerived pid) := by
  unfold timersSessionDerived
  apply discard_view_spec id (Account holders cs loans)
  exact mod_timer _ _ _ _

theorem completed (pid : PeerId) (site : HiddenSite) :
    Preserves (Account holders cs loans) (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  apply preserves_bind (del_timer pid .retransmitHandshake)
  intro _
  have first : Preserves (Account holders cs loans) (getPeer pid >>= fun p =>
      setPeer pid {p with timerHandshakeAttempts:=0,sentLastminuteHandshake:=false}) :=
    Account.update pid _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _ _ h=>h) (fun _=>rfl)
  have last (now : List UInt8) : Preserves (Account holders cs loans) (getPeer pid >>= fun p =>
      setPeer pid {p with walltimeLastHandshake:=now}) :=
    Account.update pid _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _ _ h=>h) (fun _=>rfl)
  have clock : Preserves (Account holders cs loans) (hidden site : WG.M (List UInt8)) := by
    unfold hidden
    exact hoare_liftAmbient (AmbientM.hidden site) _
  simpa only [bind_assoc] using preserves_bind first (fun _ => preserves_bind clock last)

/-- Upper uses the exact same handoff delta returned by C1's funded staging
proof. Existing caller loans remain present while durable holders are added. -/
theorem staged (account : Account holders cs loans w) (pid : PeerId) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ Account (holders.absorb delta) cs loans v := by
  obtain ⟨delta,step,funded,stable⟩ := HolderTimers.staged_funded pid account.funded account.stable a b run
  have upper : Upper holders cs (loans ++ []) w := by simpa using account.upper
  exact ⟨delta,step,funded,by simpa using upper.handoff step,stable⟩

theorem staged_boundary (pid : PeerId) : Preserves (ExactBoundary cs loans) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b account run
  cases x
  obtain ⟨holders,account⟩ := account
  obtain ⟨delta,_,post⟩ := staged account pid a b run
  exact ⟨holders.absorb delta,post⟩

private theorem source_modify (account : ExactBoundary cs loans w) (hd : w.dev=some d)
    (hp : d.peers[pid]?=some p) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) (a b : Ambient)
    (run : ((setPeer pid (f p)).run w).run a=.ok ((x,v),b)) : ExactBoundary cs loans v := by
  obtain ⟨holders,account⟩ := account
  refine ⟨holders,?_⟩
  apply (hoare_iff_run_ambient _ _ _).mp (Account.update pid f stamp count rx napi current tx) w a x v b account
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,w,a,by simp [getPeer,getDev,hd,hp],run⟩

private theorem ambient_state (action : AmbientM α) (a b : Ambient)
    (run : (((monadLift action : WG.M α)).run w).run a=.ok ((x,v),b)) : v=w :=
  (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (· = w)) w a x v b rfl run

theorem keepalive_boundary (pid : PeerId) : Preserves (ExactBoundary cs loans) (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  unfold sendKeepalive at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,run⟩ := run
  obtain ⟨same,time,d,hd,hp⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨empty,guarded,ag,guard,run⟩ := run
  have same := ambient_state (AmbientM.branch .keepaliveStagedEmpty p.staged.isEmpty) a ag guard
  subst guarded
  cases empty with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at run
    exact (hoare_iff_run_ambient _ _ _).mp (staged_boundary pid) w ag x v b hi run
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨allocated,read,aa,alloc,failed,guarded,af,guard,run⟩ := run
    have same := ambient_state (AmbientM.hiddenAlloc .keepaliveSkb) ag aa alloc
    subst read
    have same := ambient_state (AmbientM.branch .keepaliveNoMem (!allocated)) aa af guard
    subst guarded
    cases failed with
    | true =>
      simp only [ite_true] at run
      cases run
      exact hi
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨dev,read,ad,getter,u,staged,as_,write,run⟩ := run
      obtain ⟨same,time,_⟩ := DecryptCarrier.getDev_current af ad getter
      subst read
      subst ad
      have kept := source_modify hi hd hp
        (fun p => {p with staged := p.staged ++ [{mtu := dev.mtu}]})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ _ h => h) (fun _ => rfl) af as_ write
      exact (hoare_iff_run_ambient _ _ _).mp (staged_boundary pid) staged as_ x v b kept run


/-- Session key allocation changes no peer reference count. Native configured
identity, owner bounds and slot facts remain explicit source prerequisites. -/
theorem session (account : Account holders cs loans w) (pid : PeerId)
    (configured : ConfiguredIdentity.Inv w) (owners : OwnerBounds.Carrier w)
    (slots : CurrentSlots.Inv w) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    Account holders cs loans v := by
  have post := SessionCarrier.beginSession_funded pid account.funded account.stable configured owners slots a b run
  have view := (ProjectedAction.iff_run_ambient _ _ _).mp (SessionCarrier.beginSession_view pid) w a result v b run
  exact ⟨post.1,account.upper.peer_view (congrArg Prod.fst (congrArg Prod.fst view)),post.2.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
