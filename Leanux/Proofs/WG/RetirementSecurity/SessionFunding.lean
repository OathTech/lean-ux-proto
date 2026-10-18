import Leanux.Proofs.WG.RetirementSecurity.MaterialFrames
import Leanux.Proofs.WG.RetirementSecurity.Rotation

/-! The real successful session front creates its one caller-owned key
occurrence. Initialization and derivation retain that exact funding. The
front's original source factorization is the existing receipt theorem; no
future rotation success or material retention is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Credits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes

theorem entered_account (pid : PeerId) (ctx : SessionOrigin.Context) (w v : WGWorld)
    (a b : Ambient) (account : Exact credits w) (allocation : AllocationInv history w)
    (entered : SessionOrigin.Entered pid ctx w v a b) :
    Exact (⟨ctx.slot,w.keypairCounter + 1⟩ :: credits) v := by
  obtain ⟨initial,s1,a1,s2,a2,s3,a3,s4,a4,s5,a5,read,_,rejected,word,created,guard,readBack⟩ := entered
  obtain ⟨sameWorld,sameAmbient,_,_,_⟩ := Origins.getPeer_return pid w s1 initial a a1 read
  subst s1
  subst a1
  have same2 : s2 = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (sessionStateRejected initial.handshakeState) (fun g => g = w))
    w a false s2 a2 rfl rejected
  subst s2
  have same3 : s3 = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves (.handshake pid) (fun g => g = w))
    w a2 ctx.word s3 a3 rfl word
  subst s3
  have funded := account.create allocation ctx.word ctx.slot a3 a4 created
  have guarded := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .sessionNoKeypair (Option.isNone (some ctx.slot)))
      (Exact (⟨ctx.slot,w.keypairCounter + 1⟩ :: credits))) s4 a4 false s5 a5 funded guard
  exact (hoare_iff_run_ambient _ _ _).mp
    (getPeer_preserves pid (Exact (⟨ctx.slot,w.keypairCounter + 1⟩ :: credits)))
    s5 a5 ctx.peer v b guarded readBack

/-- Native session derivation is funded by the original successful create,
and no initializer resets or fabricates its reference occurrence. -/
theorem front_account (pid : PeerId) (ctx : SessionOrigin.Context) (w v : WGWorld)
    (a b : Ambient) (account : Exact credits w) (allocation : AllocationInv history w)
    (run : ((SessionOrigin.front pid).run w).run a = .ok ((some ctx,v),b)) :
    Exact (⟨ctx.slot,w.keypairCounter + 1⟩ :: credits) v := by
  obtain ⟨read,init,derive,readAmbient,initAmbient,deriveAmbient,entered,_,initRun,guard,deriveRun,_⟩ :=
    SessionOrigin.front_material pid ctx w v a b run
  have funded := entered_account pid ctx w read a readAmbient account allocation entered
  have initialized := (hoare_iff_run_ambient _ _ _).mp
    (referenceNonce_preserves _ (initKey_referenceNonce ctx.slot
      (ctx.state == HANDSHAKE_CONSUMED_RESPONSE) ctx.peer.remoteIndex) _)
    read readAmbient () init initAmbient funded initRun
  have guarded := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .sessionInitiator (ctx.state == HANDSHAKE_CONSUMED_RESPONSE))
      (Exact (⟨ctx.slot,w.keypairCounter + 1⟩ :: credits)))
    init initAmbient ctx.initiator derive deriveAmbient initialized guard
  exact (hoare_iff_run_ambient _ _ _).mp
    (referenceNonce_preserves _ (deriveKeys_referenceNonce ctx.slot ctx.initiator ctx.peer.chainingKey) _)
    derive deriveAmbient () v b guarded deriveRun

theorem front_refused_account (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (account : Exact credits w)
    (run : ((SessionOrigin.front pid).run w).run a = .ok ((none,v),b)) : Exact credits v :=
  (Origins.front_none pid w v a b run) ▸ account

theorem front_peers (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((SessionOrigin.front pid).run w).run a = .ok ((result,v),b)) : peersAt v = peersAt w := by
  cases result with
  | none => rw [Origins.front_none pid w v a b run]
  | some ctx =>
    obtain ⟨read,init,derive,readAmbient,initAmbient,deriveAmbient,entered,_,initRun,guard,deriveRun,_⟩ :=
      SessionOrigin.front_material pid ctx w v a b run
    obtain ⟨d,device,_,_,_,_,readWorld⟩ := Origins.entered_peer pid ctx w read a readAmbient entered
    have readPeers : peersAt read = peersAt w := by
      simp only [readWorld,peersAt,keyAllocationWorld,keyAllocationDevice,device,Option.map_some]
    have initPeers := (ProjectedAction.iff_run_ambient _ _ _).mp
      (initKey_peers ctx.slot (ctx.state == HANDSHAKE_CONSUMED_RESPONSE) ctx.peer.remoteIndex)
      read readAmbient () init initAmbient initRun
    have guarded : derive = init := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .sessionInitiator (ctx.state == HANDSHAKE_CONSUMED_RESPONSE))
        (fun g => g = init)) init initAmbient ctx.initiator derive deriveAmbient rfl guard
    have derivePeers := (ProjectedAction.iff_run_ambient _ _ _).mp
      (deriveKeys_peers ctx.slot ctx.initiator ctx.peer.chainingKey) derive deriveAmbient () v b deriveRun
    exact derivePeers.trans ((congrArg peersAt guarded).trans (initPeers.trans readPeers))

theorem front_peer_account (pid : PeerId) (p : Peer) (ctx : SessionOrigin.Context)
    (w v : WGWorld) (a b : Ambient) (account : PeerAccount pid p credits w)
    (allocation : AllocationInv history w)
    (run : ((SessionOrigin.front pid).run w).run a = .ok ((some ctx,v),b)) :
    PeerAccount pid p (⟨ctx.slot,w.keypairCounter + 1⟩ :: credits) v := by
  have peer := congrArg (fun maps => maps.bind fun peers => peers[pid]?) (front_peers pid w v a b run)
  simp only [peersAt,Option.bind_map,Function.comp_def] at peer
  exact ⟨peer.trans account.1,front_account pid ctx w v a b account.2 allocation run⟩

end Leanux.Proofs.WG.RetirementSecurity.Credits
