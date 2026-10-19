import Leanux.Proofs.WG.RetirementSecurity.HolderStrongFrames
import Leanux.Proofs.WG.Queues.HandshakeReceiveSlots

/-! Actual keepalive staging preserves key credit and the handshake caller's
nonfinal peer acquisition. The latter follows the source handoff equation,
including both queue admission and rejection repayment. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderKeepalive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits StackOwnership HolderConsume
variable {selected : PeerId}

def Ready (temporary : Credits.Ledger) (w : WGWorld) :=
  HolderAccount temporary w ∧ Allocated w ∧ CurrentSlots.Inv w

def Selected (temporary : Credits.Ledger) (pid : PeerId) (w : WGWorld) :=
  Ready temporary w ∧ Strong pid w

theorem staged (pid : PeerId) : Preserves (Ready temporary) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact ⟨before.1.staged before.2.1.bounded ((CurrentSlots.current before.2.2).compatible pid) a b run,
    Allocated.native (sendStagedPacketsPrefix_erases pid)
      (sendStagedPacketsPrefix_preserves_ambient allocationAmbient allocationTx pid)
      before.2.1 a b run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.sendStagedPackets_preserves pid)
      w a () v b before.2.2 run⟩

theorem staged_selected (pid : PeerId) : Preserves (Selected temporary selected) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (staged pid) w a () v b before.1 run,
    before.2.transfer (staged_send_handoff pid ((CurrentSlots.current before.1.2.2).compatible pid) a b run)⟩

theorem update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p,(f p).internalId=p.internalId)
    (fields : ∀ p,peerOwnership (f p)=peerOwnership p)
    (slots : ∀ p,Affiliation.peerCell (f p)=Affiliation.peerCell p) :
    Preserves (Ready temporary) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (HolderResponse.peer_update pid f stamp fields) w a result v b ⟨before.1,before.2.1⟩ run
  exact ⟨kept.1,kept.2,(hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer)
      pid f slots) w a result v b before.2.2 run⟩

theorem update_selected (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p,(f p).internalId=p.internalId)
    (fields : ∀ p,peerOwnership (f p)=peerOwnership p)
    (slots : ∀ p,Affiliation.peerCell (f p)=Affiliation.peerCell p)
    (count : ∀ p,(f p).refcount=p.refcount) (rx : ∀ p,(f p).rxQueue=p.rxQueue) :
    Preserves (Selected temporary selected) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (update pid f stamp fields slots) w a result v b before.1 run,
    before.2.view ((ProjectedAction.iff_run_ambient _ _ _).mp
      (peers_update pid f stamp count rx) w a result v b run)⟩

theorem ambient_state (action : AmbientM α) (a b : Ambient)
    (run : (((monadLift action : WG.M α)).run w).run a=.ok ((x,v),b)) : v=w :=
  (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (· = w)) w a x v b rfl run

/-- A source composition rule for the original keepalive, including its
allocation-failure return and its saved-peer setter before actual staging. -/
theorem rule (P : WGWorld → Prop) (pid : PeerId)
    (stage : Preserves P (sendStagedPackets pid))
    (prepare : ∀ mtu,Preserves P (getPeer pid >>= fun p =>
      setPeer pid {p with staged := p.staged ++ [{mtu:=mtu}]})) :
    Preserves P (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
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
    exact (hoare_iff_run_ambient _ _ _).mp stage w ag x v b before run
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨allocated,read,aa,alloc,failed,guarded,af,guard,run⟩ := run
    have same := ambient_state (AmbientM.hiddenAlloc .keepaliveSkb) ag aa alloc
    subst read
    have same := ambient_state (AmbientM.branch .keepaliveNoMem (!allocated)) aa af guard
    subst guarded
    cases failed with
    | true => simp only [ite_true] at run; cases run; exact before
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨dev,read,ad,getter,u,staged,as_,write,run⟩ := run
      obtain ⟨same,time,_⟩ := DecryptCarrier.getDev_current af ad getter
      subst read
      subst ad
      have paired : ((getPeer pid >>= fun p => setPeer pid {p with staged := p.staged ++ [{mtu:=dev.mtu}]}).run w).run af =
          .ok ((u,staged),as_) := by
        rw [MaterialOrigin.bind_ok_ambient]
        exact ⟨p,w,af,by simp [getPeer,getDev,hd,hp],write⟩
      have kept := (hoare_iff_run_ambient _ _ _).mp (prepare dev.mtu) w af u staged as_ before paired
      exact (hoare_iff_run_ambient _ _ _).mp stage staged as_ x v b kept run

theorem keepalive (pid : PeerId) : Preserves (Ready temporary) (sendKeepalive pid) := by
  apply rule _ pid (staged pid)
  intro mtu
  apply update <;> intro p <;> rfl

theorem keepalive_selected (pid : PeerId) : Preserves (Selected temporary selected) (sendKeepalive pid) := by
  apply rule _ pid (staged_selected pid)
  intro mtu
  apply update_selected <;> intro p <;> rfl

end Leanux.Proofs.WG.RetirementSecurity.HolderKeepalive
