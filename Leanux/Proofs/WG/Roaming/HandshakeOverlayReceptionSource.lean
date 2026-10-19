import Leanux.Proofs.WG.Roaming.HandshakeOverlayAuthenticationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Origins
variable {E F α State : Type}

theorem endpoint_appends (msg : List UInt8) (pid : PeerId) (src : SkbSource) :
    StateAppends (endpoint msg pid src) := by
  unfold endpoint EndpointAttempt.fromSkbWith
  apply StateAppends.bind (StateAppends.lift _)
  intro ep
  apply StateAppends.bind (StateAppends.lift _)
  intro success
  cases success <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact StateAppends.pure ()
  · cases ep with
    | none => exact StateAppends.lift _
    | some ep => exact EndpointAttempt.beforeCall_appends _ _ (StateAppends.focus _ _ _)

theorem appends_ite (p : Prop) [Decidable p] (yes no : PrefixM Event α)
    (hy : p → Appends yes) (hn : ¬p → Appends no) : Appends (if p then yes else no) := by
  by_cases hp : p <;> simp only [hp,ite_true,ite_false]
  · exact hy hp
  · exact hn hp

theorem response_appends (msg : List UInt8) (pid : PeerId) :
    Appends (HandshakeSources.responseWith (ops msg) pid) := by
  unfold HandshakeSources.responseWith
  dsimp only [ops]
  repeat' first
    | (overlay_action_head old; exact Appends.focus _ _ _)
    | (overlay_action_head Bind.bind; apply Appends.bind)
    | exact Appends.pure _
    | apply appends_ite
    | handshake_project_intro
    | split

theorem afterMac_appends (label msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Appends (HandshakeSources.afterMacWith (ops label) msg src loaded mac) := by
  unfold HandshakeSources.afterMacWith
  simp only [pure_bind]
  dsimp only [ops]
  repeat' first
    | (overlay_action_head HandshakeSources.responseWith; exact response_appends label _)
    | (overlay_action_head liftWGObserver; exact (endpoint_appends _ _ _).liftWGObserver)
    | (overlay_action_head old; exact Appends.focus _ _ _)
    | (overlay_action_head Bind.bind; apply Appends.bind)
    | exact Appends.pure _
    | apply appends_ite
    | handshake_project_intro
    | split

theorem receptionWith_appends (label msg : List UInt8) (src : SkbSource) :
    Appends (HandshakeSources.receptionWith (ops label) msg src) := by
  unfold HandshakeSources.receptionWith
  dsimp only [ops]
  repeat' first
    | (overlay_action_head HandshakeSources.afterMacWith; exact afterMac_appends label msg _ _ _)
    | (overlay_action_head old; exact Appends.focus _ _ _)
    | (overlay_action_head Bind.bind; apply Appends.bind)
    | exact Appends.pure _
    | apply appends_ite
    | handshake_project_intro
    | split

theorem reception_appends (msg : List UInt8) (src : SkbSource) :
    Appends (reception msg src) := receptionWith_appends msg msg src

theorem reception_valid (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun h _ => Valid h) Valid (reception msg src) := by
  intro w h prior
  obtain ⟨suffix,same⟩ := reception_appends msg src w h
  have checked := (reception_attempt msg src).under.preserves
    (attemptReception_valid msg src) w h prior
  exact ⟨suffix,same,checked⟩



end Leanux.Proofs.WG.Roaming.HandshakeOverlay
