import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolFrames

/-! Complete original response refusal with source-derived reference safety.
Only the permitted peer reference fields are excluded; endpoint, key slots,
handshake state and every peer timer field are retained, without an initialized
reference-count assumption. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def RefusalProtocol (initial : PeerId → Option Peer) (result : Option PeerId) (w : WGWorld) : Prop :=
  result = none → peerProtocolView w = initial

private theorem chain {α β : Type} (P : WGWorld → Prop) (Q : β → WGWorld → Prop)
    (action : WG.M α) (next : α → WG.M β) (ha : Preserves P action)
    (tail : ∀ x, Hoare (next x) P Q) : Hoare (action >>= next) P Q :=
  hoare_bind action next ha tail

theorem responseTail_protocol (msg : Key) (identity : StaticIdentity)
    (pid : PeerId) (initial : PeerId → Option Peer) :
    Hoare (responseTail msg identity pid)
      (fun w => peerProtocolView w = initial ∧ RepaySafe pid w) (RefusalProtocol initial) := by
  let P := fun w => peerProtocolView w = initial ∧ RepaySafe pid w
  have read (q : PeerId) : Preserves P (getPeer q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    rw [(Leanux.Proofs.WG.Queues.getPeer_normal q w v p a b run).1]
    exact hi
  have failed : Hoare (do peerPut (some pid); pure (none : Option PeerId)) P (RefusalProtocol initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run _
    rw [native_bind_run] at run
    cases paid : ((peerPut (some pid)).run w).run a with
    | error err => simp [paid] at run
    | ok out =>
      rcases out with ⟨⟨doneUnit,q⟩,c⟩
      cases doneUnit
      have frame := peerPut_protocol pid w q a c hi.2 paid
      rw [paid] at run
      cases run
      exact frame.trans hi.1
  have success (p : Peer) : Hoare (do setPeer pid p; pure (some pid)) P (RefusalProtocol initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run none
    simp only [setPeer,modifyDev,StateT.run_bind,StateT.run_modify,StateT.run_pure,
      except_ok_bind,except_pure] at run
    cases run
    cases none
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  have stop (message : String) : Hoare (invariant message : WG.M (Option PeerId)) P (RefusalProtocol initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    cases run
  unfold responseTail
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | with_reducible exact failed
    | with_reducible exact success _
    | with_reducible exact stop _
    | with_reducible exact read _
    | with_reducible exact ambient _
    | receive_crypto P
    | cookie_source_step
    | with_reducible apply chain P
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem response_refusal_protocol (msg : Key) (w v : WGWorld) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a = .ok ((none,v),b)) :
    peerProtocolView v = peerProtocolView w := by
  rw [consumeResponse_factor] at run
  cases hd : w.dev with
  | none => simp [getDev,hd,invariant,AmbientM.invariant,StateT.run_bind] at run; cases run
  | some device =>
    cases identity : device.staticIdentity.hasIdentity with
    | false =>
      simp [getDev,hd,identity,branch,branch_run,StateT.run_bind] at run
      obtain ⟨rfl,_⟩ := run
      rfl
    | true =>
      simp [getDev,hd,identity,branch,branch_run,StateT.run_bind] at run
      cases lookup : ((indexLookup [.handshake] (u32le msg 8)).run w).run
          (record a .crespNoIdentity false) with
      | error err => simp [lookup] at run
      | ok out =>
        rcases out with ⟨⟨entry,u⟩,c⟩
        have frame := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
          (indexLookup_protocol [.handshake] (u32le msg 8)) w _ entry u c lookup
        have loan := (hoare_iff_run_ambient _ _ _).mp
          (indexLookup_loan [.handshake] (u32le msg 8) w) w _ entry u c rfl lookup
        cases entry with
        | none =>
          simp [lookup] at run
          obtain ⟨rfl,_⟩ := run
          exact frame
        | some entry =>
          rcases entry with ⟨owner,pid⟩
          cases owner with
          | keypair kid => simp [lookup,invariant,AmbientM.invariant] at run; cases run
          | handshake owner =>
            simp only [lookup,except_ok_bind,Option.isNone_some] at run
            exact (hoare_iff_run_ambient _ _ _).mp
              (responseTail_protocol msg device.staticIdentity pid (peerProtocolView w))
              u _ none v b ⟨frame,loan_repay_safe w u pid loan⟩ run rfl

theorem receive_response_refused_protocol (msg : Key) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (load : (Cookies.loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeResponse msg).run q).run (responseConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),record d .hsRespNoPeer true) ∧
      peerProtocolView v = peerProtocolView w ∧ v.sent = w.sent := by
  let observe := fun pair : WGStoreView × (PeerId → Option Peer) =>
    fun pid => (pair.2 pid).map protocolPeer
  have macFrame : SameView peerProtocolView (cookieValidatePacket msg src loaded) :=
    (cookieValidatePacket_quiet msg src loaded).of_factor observe peerProtocolView (fun _ => rfl)
  have loadFrame : SameView peerProtocolView Cookies.loadPhase :=
    Cookies.loadPhase_sameStore.of_factor
      (fun s => fun pid => (s.dev.bind fun dev => dev.peers[pid]?).map protocolPeer)
      peerProtocolView (fun _ => rfl)
  have loadSame := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    loadFrame w _ loaded u b load
  have macSame := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    macFrame u b _ q c mac
  have noiseSame := response_refusal_protocol msg q v _ d refused
  have silent := receive_response_refused_sent msg src loaded w u q v a b c d kind load mac refused
  exact ⟨silent.1,noiseSame.trans (macSame.trans loadSame),silent.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects
