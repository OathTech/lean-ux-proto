import Leanux.Proofs.WG.Queues.HandshakeAfterMac
import Leanux.Proofs.WG.Queues.HandshakeCookiePayment

/-! Normal execution of the unchanged handshake receiver retains complete
holder funding and stable RX. Entry support is supplied at the actual input. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeReception
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HandshakeResponse

private theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Input cs loans) action := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join)
  · exact HolderEncrypt.native_boundary (HolderEncrypt.store_fields same)
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
    · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.store) action same
    · exact CurrentSlots.view_preserves (project := id) (Affiliation.kernel (project := id) same)

private theorem cookie {action : WG.M α} (same : SameCookie action) : Preserves (Input cs loans) action := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join)
  · exact HandshakeAfterMac.cookie_boundary same
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
    · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.cookie) action same
    · apply CurrentSlots.fields_preserves (project := id)
      apply same.of_factor (fun k : WGOwnedView => CurrentSlots.fields {dev:=k.dev})
      intro w
      unfold CurrentSlots.fields Queues.RxCredits.keyWords cookieView cookieDevice wgOwnedView wgStoreView
      cases hd : w.dev <;> simp [hd]


/-- No receive-endpoint premise is assumed. Session allocation receives its
configured/frontier/slot facts from Entry along the actual preceding source. -/
theorem receive (msg : List UInt8) (src : SkbSource) :
    Hoare (receiveHandshakePacket msg src) (Input cs loans) (fun _ => Boundary cs loans) := by
  rw [Cookies.receive_factor]
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsCookie _) (Input cs loans))
  intro isCookie
  cases isCookie with
  | true =>
    apply hoare_bind _ _ (hoare_consequence (HandshakeCookiePayment.consume msg)
      (fun _ hi => hi.1) (fun _ _ hi => hi))
    intro _
    exact preserves_pure ()
  | false =>
    apply hoare_bind _ _ (store Cookies.loadPhase_sameStore)
    intro loaded
    apply hoare_bind _ _ (cookie (cookieValidatePacket_sameCookie msg src loaded))
    intro mac
    exact HandshakeAfterMac.afterMac msg src loaded mac

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeReception
