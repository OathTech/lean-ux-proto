import Leanux.Proofs.WG.Index.ResponseIndexEffects
import Leanux.Proofs.WG.Index.SenderIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem endpointBounds_modifyPeer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p) :
    Ensures (modifyPeer pid f)
      (fun g => ∀ d,g.dev=some d → InitializedBounds.EndpointBounds d)
      (fun _ g => ∀ d,g.dev=some d → InitializedBounds.EndpointBounds d) :=
  modifyPeer_device_predicate pid InitializedBounds.EndpointBounds f
    (fun d p resident pre => endpointBounds_affiliation d _
      (Affiliation.state_peer_same d pid p (f p) resident (same p)) pre)

theorem addMacToPacket_spec_affiliation_variant (pid : PeerId) (msg : List UInt8) :
    SameView Affiliation.view (addMacToPacket pid msg) := by
  intro initial
  let P := fun w => Affiliation.view w = initial
  have test (p : Peer) : Preserves P
      (WG.andM (branch .addMacCookieValid p.cookieIsValid)
        (branchExpired .addMacCookieFresh p.cookieBirthdate COOKIE_FRESH_SECONDS (!·))) :=
    DumpComposition.andM_sameView _ _
      (fun k => hoare_liftAmbient (AmbientM.branch .addMacCookieValid p.cookieIsValid)
        (fun w => Affiliation.view w=k))
      ((branchExpired_sameWGWorld _ _ _ (!·)).factor (fun s => s.dev.map Affiliation.state)) initial
  change Preserves P _
  unfold addMacToPacket
  apply hoare_bind _ _ (Affiliation.getPeer_spec (fun v => v=initial) pid)
  intro p
  apply hoare_bind _ _ (Affiliation.setPeer_spec (fun v => v=initial) pid _)
  intro _
  apply hoare_bind _ _ (test p)
  intro accepted
  split <;> exact preserves_pure _

theorem endpointBounds_view_frame {α : Type} (action : WG.M α)
    (same : SameView Affiliation.view action) :
    Ensures action
      (fun g => ∀ d,g.dev=some d → InitializedBounds.EndpointBounds d)
      (fun _ g => ∀ d,g.dev=some d → InitializedBounds.EndpointBounds d) := by
  intro w a x v b pre run e final
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp same w a x v b run
  cases device : w.dev with
  | none => simp [Affiliation.view,device,final] at frame
  | some d =>
    have equal : Affiliation.state e=Affiliation.state d := by
      simpa [Affiliation.view,device,final] using frame
    exact endpointBounds_affiliation d e equal (pre d device)

theorem sender_modPeerTimer (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) : SameView senderFields (modPeerTimer site pid timer delay) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a value out b run
  cases device : g.dev with
  | none =>
    exact False.elim (ResponseSuffix.modPeerTimer_missing_false site pid timer delay g out a b value
      (by simp [peerAt,device]) run)
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      exact False.elim (ResponseSuffix.modPeerTimer_missing_false site pid timer delay g out a b value
        (by simp [peerAt,device,resident]) run)
    | some p =>
      obtain ⟨allowed,effect⟩ := TimerDiscipline.modPeerTimer_effect site pid timer delay
        d p resident (Campaign2.snapshot g a) g a value out b ⟨rfl,device⟩ run
      cases value with
      | false => exact congrArg senderStateFields effect
      | true =>
        exact senderStateFields_armEffect (Campaign2.snapshot g a) d pid p timer delay
          (Campaign2.snapshot out b).wg device resident effect

theorem sender_derived (pid : PeerId) : SameView senderFields (timersSessionDerived pid) :=
  (sender_modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).map (fun _ => ())

theorem responseIndex_sender_frame {α : Type} (action : WG.M α)
    (frame : SameView senderFields action) :
    Ensures action ResponseIndexState (fun _ => ResponseIndexState) :=
  senderFrame_device_predicate action frame _
    (fun d e same pre =>
      ⟨(senderDeviceCell_transports d e [] 0 same).1 pre.1,
        senderDeviceCell_coherent d e same pre.2.1,
        (senderDeviceCell_transports d e [] 0 same).2.1 pre.2.2⟩)

theorem responsePrefix_sender_frame {α : Type} (pid : PeerId) (action : WG.M α)
    (bounds : Ensures action
      (fun g => ∀ d,g.dev=some d → InitializedBounds.EndpointBounds d)
      (fun _ g => ∀ d,g.dev=some d → InitializedBounds.EndpointBounds d))
    (frame : SameView senderFields action) :
    Ensures action (ResponseIndexPrefix pid) (fun _ => ResponseIndexPrefix pid) := by
  intro g a value out b pre run
  have transported := senderFrame_device_predicate action frame
    (fun d => HandshakeCompatible pid d ∧ HashSlotCoverage d ∧ DeadHashedReserved [] d)
    (fun d e same held =>
      ⟨(senderDeviceCell_transports d e [] pid same).2.2 held.1,
        (senderDeviceCell_transports d e [] pid same).1 held.2.1,
        (senderDeviceCell_transports d e [] pid same).2.1 held.2.2⟩)
    g a value out b (fun d device => ⟨pre.2.1 d device,pre.2.2.1 d device,pre.2.2.2 d device⟩) run
  exact ⟨bounds g a value out b pre.1 run,
    fun d device => (transported d device).1,
    fun d device => (transported d device).2.1,
    fun d device => (transported d device).2.2⟩

end Leanux.Proofs.WG.Index
