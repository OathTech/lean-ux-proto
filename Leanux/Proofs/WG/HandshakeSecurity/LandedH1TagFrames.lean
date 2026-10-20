import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1TrafficFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverFacts
import Leanux.Proofs.WG.Noise.Statements

/-! Adapters from campaign 2 H1 as landed on main (be8c209c, shared carries
through ac55c7d5). These inhabit the local tag packages without an initialized
security assumption. The native C2 declarations remain the proof dependencies. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.LandedH1
open Leanux Leanux.WG Leanux.Proofs.Framing

private theorem same {α : Type} {action : WG.M α}
    (frame : ∀ entry, Noise.Ensures action
      (fun w => Noise.responseTagMap w.dev = Noise.responseTagMap entry)
      (fun _ w => Noise.responseTagMap w.dev = Noise.responseTagMap entry)) :
    H1TagSame action := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact (frame w.dev w a value v b rfl run).trans before

private theorem retained {α : Type} {action : WG.M α}
    (frame : ∀ entry, Preserves (Noise.DriverTags.Silent.Retained entry) action) :
    H1TagRetains action := by
  intro w v a b value run pid tag found _
  exact (hoare_iff_run_ambient _ _ _).mp (frame (handshakeTagAt w))
    w a value v b (Noise.TagsRetained.refl _) run pid tag found

private theorem productRetained {α : Type} {action : Leanux.M α}
    (frame : ∀ entry, Preserves
      (fun w : World => Noise.DriverTags.Silent.Retained entry w.wg) action) :
    H1ProductTagRetains action := by
  intro w value v run pid tag found _
  exact (hoare_iff_run _ _ _).mp (frame (handshakeTagAt w.wg))
    w value v (Noise.TagsRetained.refl _) run pid tag found

/-- Landed H1's normal-call tag frames supply every handshake suffix premise. -/
theorem handshake : H1HandshakeTagFrames where
  mac := fun pid msg => same (Noise.addMacToPacket_spec_tagMap_variant pid msg)
  send := fun pid msg => same (Noise.sendBufferToPeer_spec_tagMap_variant pid msg)
  traversal := fun pid => same (Noise.ResponseSuffix.traversal_tag_frame pid)
  initiated := fun pid => same (Noise.InitiationCaller.timersHandshakeInitiated_spec_tagMap_variant pid)
  derived := fun pid => same (Noise.ResponseSuffix.derived_tag_frame pid)
  deleteTimer := fun pid timer => same (Noise.ResponseSuffix.delTimer_tag_frame pid timer)
  endpoint := fun pid src => same (Noise.ReceptionTagSupport.setPeerEndpointFromSkb_tag_frame pid src)
  complete := fun pid site => same (Noise.ReceptionTagSupport.handshakeComplete_tag_frame pid site)
  cookieConsume := fun msg => same (Noise.ReceptionTagSupport.cookieMessageConsume_tag_frame msg)
  cookie := fun msg src => same (Noise.sendHandshakeCookie_spec_tagMap_variant msg src)
  validate := fun msg src loaded => same (Noise.cookieValidatePacket_spec_tagMap_variant msg src loaded)

/-- Landed H1/H2 staging and completion facts supply the data tag premises. -/
theorem data : H1DataTagFrames where
  staging := by
    intro pid w v a b value run q tag found _
    exact Index.sendStagedPackets_tags_retained pid w a value v b run q tag found
  keepalive := by
    intro pid w v a b value run q tag found _
    exact Index.sendKeepalive_tags_retained pid w a value v b run q tag found
  consume := fun pid pkt ep => retained (fun entry =>
    Noise.DriverTags.Silent.consumeDataDone_retained entry pid pkt ep)

/-- Landed H1 worker contracts supply the native data-worker tag premises. -/
theorem workers : H1WorkerTagFrames where
  poll := fun pid budget => productRetained (fun entry => Noise.DriverTags.Poll.poll_native entry pid budget)
  softirq := productRetained Noise.DriverTags.Poll.softirq_native
  inlinePoll := productRetained Noise.DriverTags.Poll.inline_native
  irqExit := productRetained Noise.DriverTags.Poll.irqExit_native
  txStep := fun pid => retained (fun entry => Noise.DriverTags.Silent.txStep_retained entry pid)
  decryptPrepare := retained Noise.DriverTags.Silent.decryptPrepare_retained
  enqueue := fun item state => retained (fun entry => Noise.DriverTags.Silent.enqueue_retained entry item state)
  encryptPacket := fun kid pkt => productRetained (fun entry => Noise.DriverTags.Silent.encryptPacket_retained entry kid pkt)

/-- Landed clearing/expiry may zero a tag, but cannot restore an old exchange. -/
theorem clear : ∀ pid, H1TagRetains (handshakeClear pid) := by
  intro pid w v a b value run q tag found nonzero
  have effect := Noise.handshakeClear_tagMap pid w.dev w a value v b rfl run q
  change handshakeTagAt v q = _ at effect
  rw [effect] at found
  split at found
  · cases found
    exact False.elim (nonzero rfl)
  · exact found

/-- Landed H1 control frames supply the local control package. -/
theorem control : H1ControlTagFrames where
  clear := clear
  clearKeys := Noise.DriverTags.Flush.keys_tags
  timer := fun pid timer => retained (fun entry => Noise.DriverTags.Silent.timerCallback_retained entry pid timer)
  makeDead := Noise.DriverTags.Removal.makeDead_tags
  free := Noise.DriverTags.free_frame

/-- Landed H1 creation and expiry facts discharge all configuration tag fields. -/
theorem configuration : H1ConfigurationTagFrames where
  allowed := Noise.DriverTags.setAllowedip_frame
  removeIps := Noise.DriverTags.removeByPeer_frame
  endpoint := Noise.DriverTags.setPeerEndpoint_frame
  peerGet := Noise.DriverTags.peerGet_frame
  create := by
    intro key psk w v a b value run q tag found nonzero
    have effect := Noise.peerCreate_tag_map key psk (Campaign2.snapshot w a)
      w a value v b rfl run q
    change handshakeTagAt v q = _ at effect
    rw [effect] at found
    cases value with
    | error e => exact found
    | ok pid =>
      change (if pid = q then some HANDSHAKE_ZEROED else handshakeTagAt w q) = some tag at found
      by_cases equal : pid = q
      · rw [ite_eq_left equal] at found
        exact False.elim (nonzero (Option.some.inj found).symm)
      · simpa only [ite_eq_right equal] using found
  precompute := Noise.DriverTags.precomputeStaticStatic_frame
  expire := by
    intro pid w v a b value run q tag found nonzero
    have effect := Noise.expireCurrentPeerKeypairs_tagMap_projected pid (Campaign2.snapshot w a)
      w a value v b rfl run q
    change handshakeTagAt v q = _ at effect
    rw [effect] at found
    split at found
    · cases found
      exact False.elim (nonzero rfl)
    · exact found
  clearEndpoint := Noise.DriverTags.clearPeerEndpointSrc_frame
  port := Noise.DriverTags.setPort_frame

/-- Landed H1 traffic contracts discharge ingress, transmit, dump and cleanup. -/
theorem traffic : H1TrafficTagFrames where
  receive := fun msg src => retained (fun entry => Noise.DriverTags.Traffic.receive_retained entry msg src)
  transmit := by
    intro family addr packets mtu w v a b value run q tag found _
    exact Noise.DriverTags.Transmit.retained family addr packets mtu w a value v b run q tag found
  dump := by
    intro action w v a b value run q tag found _
    exact Noise.DriverTags.Dump.retained action w a value v b run q tag found
  create := retained Noise.DriverTags.Environment.create_native
  cleanup := productRetained Noise.DriverTags.Environment.cleanup_native

end Leanux.Proofs.WG.HandshakeSecurity.LandedH1
