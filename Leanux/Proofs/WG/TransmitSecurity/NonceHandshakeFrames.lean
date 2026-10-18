import Leanux.Proofs.WG.TransmitSecurity.NonceCallerFrames
import Leanux.Proofs.WG.Keypairs.Frames.WGMore
import Leanux.Proofs.WG.Cookies.Gate

/-! Native handshake and timer leaves retain sending allocation history.
Only beginSession creates an identity and keepalive staging allocates nonces. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem full {α : Type} {a : WG.M α} (keys : SameView Origins.view a)
    (frontier : Keypairs.SameSnapshot a) : SameView view a :=
  reference_frame (RetirementSecurity.full_keys_frontier_frame a keys frontier)

theorem maybe_peer (pid : Option PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (peerGetMaybeZero pid) := by
  unfold peerGetMaybeZero refcountIncNotZero
  simp (config := {zeta := false}) only [requireNotPending,branch,branchCmp,invariant,unsupported,pure_bind]
  repeat' nonce_preserves_step h

theorem pubkey (key : Key) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact maybe_peer _ h)
    | nonce_preserves_step h

theorem owner_write (o : IndexOwner) (pid : Option PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (o.setPeerWord pid) := by
  cases o with
  | handshake id =>
    change Preserves _ (do let p ← getPeer id; setPeer id {p with handshakeEntryPeer := pid})
    exact native_frame h ((peer_read id).bind fun p => peer_write id {p with handshakeEntryPeer := pid})
  | keypair id => exact native_frame h (update_key id (fun k => {k with peer := pid}) (fun _ => rfl))

theorem index_lookup (kinds : List IndexKind) (idx : Nat) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (indexLookup kinds idx) := by
  unfold indexLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact maybe_peer _ h)
    | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
    | (rx_retention_head IndexOwner.setPeerWord; exact owner_write _ _ h)
    | (rx_retention_head liftIndex; exact native_frame h (index _))
    | nonce_preserves_step h

private theorem conditional {α : Type} (p : Prop) [Decidable p] (a b : WG.M α)
    (P : WGWorld → Prop) (ha : Preserves P a) (hb : Preserves P b) :
    Preserves P (if p then a else b) := by
  by_cases h : p <;> simp only [h,↓reduceIte] <;> assumption

macro "nonce_handshake_step " h:term : tactic => `(tactic| first
  | (rx_retention_head ite; apply conditional)
  | (rx_retention_head pubkeyLookup; exact pubkey _ $h)
  | (rx_retention_head indexLookup; exact index_lookup _ _ $h)
  | (rx_retention_head messageEphemeral; exact native_frame $h ((messageEphemeral_sameWGWorld _ _ _ _).factor view))
  | (rx_retention_head mixDh; exact native_frame $h ((mixDh_sameWGWorld _ _ _ _).factor view))
  | (rx_retention_head mixPrecomputedDh; exact native_frame $h ((mixPrecomputedDh_sameWGWorld _ _).factor view))
  | (rx_retention_head messageDecrypt; exact native_frame $h ((messageDecrypt_sameWGWorld _ _ _).factor view))
  | (rx_retention_head kdf; exact native_frame $h ((kdf_sameWGWorld _ _ _ _).factor view))
  | (rx_retention_head kdfOut; exact native_frame $h ((kdfOut_sameWGWorld _ _).factor view))
  | nonce_preserves_step $h)

theorem initiation (msg : List UInt8) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (consumeInitiation msg) := by
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,hiddenClock64]
  repeat' nonce_handshake_step h

theorem response (msg : List UInt8) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' nonce_handshake_step h

theorem cookie_consume (msg : List UInt8) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,invariant,hiddenClock64]
  repeat' nonce_handshake_step h

theorem create_response (pid : PeerId) : SameView view (createResponse pid) :=
  full (Origins.Retaining.createResponse_material pid)
    (Keypairs.WGTransitions.createResponse_sameSnapshot pid)

theorem mac (pid : PeerId) (msg : List UInt8) : SameView view (addMacToPacket pid msg) :=
  full (Origins.Retaining.addMacToPacket_material pid msg)
    (Keypairs.WGTransitions.addMacToPacket_sameSnapshot pid msg)

theorem send_buffer (pid : PeerId) (bytes : List UInt8) : SameView view (sendBufferToPeer pid bytes) :=
  full (Origins.Retaining.sendBufferToPeer_material pid bytes)
    (Keypairs.WGTransitions.sendBufferToPeer_sameSnapshot pid bytes)

theorem derived (pid : PeerId) : SameView view (timersSessionDerived pid) :=
  full (Origins.Retaining.timersSessionDerived_material pid)
    (Keypairs.WGTransitions.timersSessionDerived_sameSnapshot pid)

theorem traversal (pid : PeerId) : SameView view (timersTraversal pid) :=
  full (Origins.Retaining.timersTraversal_material pid)
    (Keypairs.WGTransitions.timersTraversal_sameSnapshot pid)

theorem sent (pid : PeerId) : SameView view (timersAnyAuthenticatedPacketSent pid) :=
  full (Origins.Retaining.timersAnyAuthenticatedPacketSent_material pid)
    (Keypairs.WGTransitions.timersAnyAuthenticatedPacketSent_sameSnapshot pid)

theorem received (pid : PeerId) : SameView view (timersAnyAuthenticatedPacketReceived pid) :=
  full (Origins.Retaining.timersAnyAuthenticatedPacketReceived_material pid)
    (Keypairs.WGTransitions.timersAnyAuthenticatedPacketReceived_sameSnapshot pid)

theorem complete (pid : PeerId) (site : HiddenSite) : SameView view (timersHandshakeComplete pid site) :=
  full (Origins.Retaining.timersHandshakeComplete_material pid site)
    (Keypairs.WGTransitions.timersHandshakeComplete_sameSnapshot pid site)

theorem cookie_frame {α : Type} {a : WG.M α} (frame : Cookies.NoNoiseChange a) : SameView view a := by
  apply frame.of_factor
    (fun s => View.mk s.2.2 (fun id => (s.1.bind fun d => d.keypairs[id]?).map Nonce.cell)) view
  intro w
  simp only [view,Cookies.noiseView,Cookies.viewOfStore,wgStoreView,Cookies.scrub,
    Option.bind_map,Function.comp_def]

theorem cookie_send (msg : List UInt8) (src : SkbSource) :
    SameView view (sendHandshakeCookie msg src) := cookie_frame (Cookies.sendHandshakeCookie_frame msg src)

theorem cookie_validate (msg : List UInt8) (src : SkbSource) (loaded : Bool) :
    SameView view (cookieValidatePacket msg src loaded) := by
  apply full
  · exact Origins.Retaining.cookie_material_native _
      ((cookieValidatePacket_sameCookie msg src loaded).factor WGOwnedView.toWGStoreView)
  · exact Keypairs.WGMore.cookieValidatePacket_sameSnapshot msg src loaded

theorem load : SameView view Cookies.loadPhase := store Cookies.loadPhase_sameStore

theorem endpoint (pid : PeerId) (src : SkbSource) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact native_frame h (store (endpointFromSkb_sameWGStore _)))
    | (rx_retention_head setPeerEndpoint; exact native_frame h (full
        (Origins.Retaining.setPeerEndpoint_material _ _) (Keypairs.WGFrames.setPeerEndpoint_sameSnapshot _ _)))
    | nonce_handshake_step h

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
