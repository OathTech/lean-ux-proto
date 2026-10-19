import Leanux.Proofs.WG.RetirementSecurity.HolderCookieConsume

/-! Exact key-credit transport through the complete original handshake
receive packet, including cookie lookup/reply, load bookkeeping, both Noise
arms and each actual final peer payment. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits StackOwnership

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Ready temporary) action :=
  combine (ReceiveEntry.store same)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.store) action same)

theorem cookie_frame {action : WG.M α} (same : SameCookie action) : Preserves (Ready temporary) action := by
  have points : SameView ownershipPointView action := same.of_factor
    (fun s : WGOwnedView => ownershipPointView {dev:=s.dev}) ownershipPointView
    (fun w => by
      simp [ownershipPointView,ownershipAt,peerAt,packetKeyWords,
      cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def]
      funext id
      simp [RetirementSecurity.keyReferenceView,RetirementSecurity.keyAt,cookieDevice,Option.bind_map,Function.comp_def])
  apply combine
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    obtain ⟨h,allocation⟩ := before.2
    have frame := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
    exact ⟨before.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp points w a result v b run),
      ⟨h,allocationCookieStable h w v (congrArg WGOwnedView.toWGStoreView frame) allocation⟩⟩
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.cookie) action same

theorem cookie_reply (msg : List UInt8) (src : SkbSource) : Preserves (Ready temporary) (sendHandshakeCookie msg src) := by
  have points : SameView ownershipPointView (sendHandshakeCookie msg src) :=
    (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => ownershipPointView {dev:=s.1}) ownershipPointView
      (fun w => by
        simp [ownershipPointView,ownershipAt,peerAt,packetKeyWords,
        Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.bind_map,Function.comp_def]
        funext id
        simp [RetirementSecurity.keyReferenceView,RetirementSecurity.keyAt,Cookies.scrub,Option.bind_map,Function.comp_def])
  exact combine (HolderResponse.points (HandshakeReceiveCall.erases (.cookie msg src))
      (HandshakeReceiveCall.allocation (.cookie msg src)) points)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.sendCookie) msg src)

theorem cookie_consume (msg : List UInt8) : Preserves (Ready temporary) (cookieMessageConsume msg) :=
  combine (HolderResponse.join (cookieMessageConsumePrefix_erases msg)
    (cookieMessageConsumePrefix_preserves allocationAmbient msg) (HolderConsume.cookie msg))
    (HandshakeEntry.cookie msg)

theorem weaken {action : WG.M α} (keeps : Preserves (Ready temporary) action) :
    Hoare action (Ready temporary) (fun _ => HolderAccount temporary) :=
  hoare_consequence keeps (fun _ before=>before) (fun _ _ before=>before.1.1)

theorem after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Hoare (Cookies.afterMac msg src loaded mac) (Ready temporary) (fun _ => HolderAccount temporary) := by
  rw [HandshakeAfterMac.source_factor]
  unfold HandshakeAfterMac.source WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head HandshakeArms.initiation; exact initiation_arm msg src)
    | (index_material_head HandshakeArms.response; exact response_arm msg src)
    | (index_material_head sendHandshakeCookie; first | exact cookie_reply msg src | exact weaken (cookie_reply msg src))
    | (index_material_head HandshakeReceive.finishSelected
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a result v b before run
       cases run)
    | (index_material_head Pure.pure; first | exact preserves_pure _ | exact weaken (preserves_pure _))
    | (index_material_head Bind.bind; apply hoare_bind)
    | loan_crypto (Ready temporary)
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

theorem receive_keys (msg : List UInt8) (src : SkbSource) :
    Hoare (receiveHandshakePacket msg src) (Ready temporary) (fun _ => HolderAccount temporary) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head cookieMessageConsume; first | exact cookie_consume _ | exact weaken (cookie_consume _))
    | (index_material_head Cookies.loadPhase; exact store Cookies.loadPhase_sameStore)
    | (index_material_head cookieValidatePacket; exact cookie_frame (cookieValidatePacket_sameCookie _ _ _))
    | (index_material_head Cookies.afterMac; exact after_mac _ _ _ _)
    | (index_material_head getDev; exact store getDev_sameWGStore)
    | (index_material_head Pure.pure; first | exact preserves_pure _ | exact weaken (preserves_pure _))
    | (index_material_head Bind.bind; apply hoare_bind)
    | loan_crypto (Ready temporary)
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

/-- Native handshake receipt closes every local key-reference obligation;
its caller must still provide the independently initialized boundary. -/
theorem receive (msg : List UInt8) (src : SkbSource) : Preserves (Ready temporary) (receiveHandshakePacket msg src) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp (receive_keys msg src) w a result v b before run,
    Allocated.native (HandshakeReceiveCall.erases (.packet msg src))
      (HandshakeReceiveCall.allocation (.packet msg src)) before.1.2 a b run⟩,
    (hoare_iff_run_ambient _ _ _).mp (HandshakeReceiveSlots.receive msg src) w a result v b before.2 run⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderReceive
