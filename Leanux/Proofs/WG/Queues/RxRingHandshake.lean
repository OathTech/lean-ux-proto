import Leanux.Proofs.WG.Queues.RxRingTx
import Leanux.Proofs.WG.Lifetimes.CookieAccess
import Leanux.Proofs.WG.Cookies.Gate

/-! The handshake worker never admits transport data. These concrete full
RX-cell frames cover its cookie, Noise, session, reply and TX-staging callees.
Malformed types and every original Stop remain executable source outcomes. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem cookie_frame {a : Leanux.M α} (ha : SameView productCookieView a) : SameView cell a := by
  apply ha.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex, d.decryptQueue))
    cell
  intro w
  simp only [productCookieView, cookieStoreView, cookieView, wgOwnedView,
    wgStoreView, cookieDevice, cell, Option.map_map, Function.comp_def]

theorem cookie_native_frame {a : WG.M α} (ha : SameCookie a) : SameView nativeCell a := by
  apply ha.of_factor (fun store : WGOwnedView => store.dev.map fun d => (d.ifindex, d.decryptQueue))
    nativeCell
  intro w
  simp only [cookieView, wgOwnedView, wgStoreView, cookieDevice, nativeCell,
    Option.map_map, Function.comp_def]

theorem pubkeyLookup_cell key : SameView nativeCell (pubkeyLookup key) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_pg := fun id => (peerGetMaybeZero_frame id).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, pubkeyLookup, getDev, h_pg, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem consumeInitiation_cell msg : SameView nativeCell (consumeInitiation msg) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_put := fun id => (peerPut_frame id).wp (fun t => t = s)
  have h_eph := fun b e ck h => ((messageEphemeral_sameWGWorld b e ck h).factor nativeCell).wp (fun t => t = s)
  have h_dh := fun b ck p q => ((mixDh_sameWGWorld b ck p q).factor nativeCell).wp (fun t => t = s)
  have h_pre := fun ck p => ((mixPrecomputedDh_sameWGWorld ck p).factor nativeCell).wp (fun t => t = s)
  have h_dec := fun a k h => ((messageDecrypt_sameWGWorld a k h).factor nativeCell).wp (fun t => t = s)
  have h_look := fun k => (pubkeyLookup_cell k).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, consumeInitiation, getDev, h_gp, h_sp, h_put, h_eph, h_dh, h_pre, h_dec, h_look, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem consumeResponse_cell msg : SameView nativeCell (consumeResponse msg) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_put := fun id => (peerPut_frame id).wp (fun t => t = s)
  have h_lookup := fun ks i => (indexLookup_frame ks i).wp (fun t => t = s)
  have h_eph := fun b e ck h => ((messageEphemeral_sameWGWorld b e ck h).factor nativeCell).wp (fun t => t = s)
  have h_dh := fun b ck p q => ((mixDh_sameWGWorld b ck p q).factor nativeCell).wp (fun t => t = s)
  have h_dec := fun a k h => ((messageDecrypt_sameWGWorld a k h).factor nativeCell).wp (fun t => t = s)
  have h_kdf := fun b c ck d => ((Framing.kdf_sameWGWorld b c ck d).factor nativeCell).wp (fun t => t = s)
  have h_out := fun xs i => ((Framing.kdfOut_sameWGWorld xs i).factor nativeCell).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, consumeResponse, getDev, h_gp, h_sp, h_put, h_lookup, h_eph, h_dh, h_dec, h_kdf, h_out, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem createResponse_cell pid : SameView nativeCell (createResponse pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_pub := fun k => ((generatePublic_sameWGWorld k).factor nativeCell).wp (fun t => t = s)
  have h_eph := fun b e ck h => ((messageEphemeral_sameWGWorld b e ck h).factor nativeCell).wp (fun t => t = s)
  have h_dh := fun b ck p q => ((mixDh_sameWGWorld b ck p q).factor nativeCell).wp (fun t => t = s)
  have h_kdf := fun b c ck d => ((Framing.kdf_sameWGWorld b c ck d).factor nativeCell).wp (fun t => t = s)
  have h_out := fun xs i => ((Framing.kdfOut_sameWGWorld xs i).factor nativeCell).wp (fun t => t = s)
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  have h_owner := fun o => indexOwner_peerDeref_preserves o (fun w => nativeCell w = s)
  unfold Preserves Hoare at h_owner
  have h_word := fun o => indexOwner_peerWord_preserves o (fun w => nativeCell w = s)
  unfold Preserves Hoare at h_word
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, h_owner, h_word, h_gp, h_sp, h_pub, h_eph, h_dh, h_kdf, h_out, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem addMacToPacket_cell pid msg : SameView nativeCell (addMacToPacket pid msg) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_exp := fun d b n f => ((branchExpired_sameWGWorld d b n f).factor nativeCell).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, addMacToPacket, h_gp, h_sp, h_exp, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem keypairCreate_cell pid : SameView nativeCell (keypairCreate pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_sk := fun id k => (setKeypair_cell id k).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, keypairCreate, getDev, modifyDev, h_sk, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem addNewKeypair_cell pid kp : SameView nativeCell (addNewKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_gk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have h_kput := fun id b => (keypairPut_frame id b).wp (fun t => t = s)
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, h_gp, h_sp, h_gk, h_kput, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem deriveKeys_cell kp initiator ck : SameView nativeCell (deriveKeys kp initiator ck) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have h_sk := fun id k => (setKeypair_cell id k).wp (fun t => t = s)
  have h_kdf := fun b c ck d => ((Framing.kdf_sameWGWorld b c ck d).factor nativeCell).wp (fun t => t = s)
  have h_out := fun xs i => ((Framing.kdfOut_sameWGWorld xs i).factor nativeCell).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, deriveKeys, h_gk, h_sk, h_kdf, h_out, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem handshakeZero_cell pid : SameView nativeCell (handshakeZero pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, handshakeZero, h_gp, h_sp, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem beginSession_cell pid : SameView nativeCell (beginSession pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_gk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have h_sk := fun id k => (setKeypair_cell id k).wp (fun t => t = s)
  have h_create := fun p => (keypairCreate_cell p).wp (fun t => t = s)
  have h_derive := fun k b ck => (deriveKeys_cell k b ck).wp (fun t => t = s)
  have h_zero := fun p => (handshakeZero_cell p).wp (fun t => t = s)
  have h_add := fun p k => (addNewKeypair_cell p k).wp (fun t => t = s)
  have h_owner := fun o => indexOwner_peerDeref_preserves o (fun w => nativeCell w = s)
  unfold Preserves Hoare at h_owner
  have h_word := fun o => indexOwner_peerWord_preserves o (fun w => nativeCell w = s)
  unfold Preserves Hoare at h_word
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, h_owner, h_word, beginSession, h_gp, h_sp, h_gk, h_sk, h_create, h_derive, h_zero, h_add, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem timersSessionDerived_cell pid : SameView nativeCell (timersSessionDerived pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_mod := fun site p t n => (modPeerTimer_cell site p t n).wp (fun t => t = s)
  have hd (α : Type) := discard_view_spec (m := AmbientM) nativeCell (α := α) (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, timersSessionDerived, h_mod, hd]

theorem sendBufferToPeer_cell pid bytes : SameView nativeCell (sendBufferToPeer pid bytes) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_four := fun e => (send4_cell e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  have h_six := fun e => (send6_cell e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, sendBufferToPeer, h_gp, h_sp, h_four, h_six, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem sendHandshakeResponse_cell pid : SameView nativeCell (sendHandshakeResponse pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_create := fun p => (createResponse_cell p).wp (fun t => t = s)
  have h_mac := fun p msg => (addMacToPacket_cell p msg).wp (fun t => t = s)
  have h_begin := fun p => (beginSession_cell p).wp (fun t => t = s)
  have h_session := fun p => (timersSessionDerived_cell p).wp (fun t => t = s)
  have h_trav := fun p => (timersTraversal_cell p).wp (fun t => t = s)
  have h_sent := fun p => (timersAnyAuthenticatedPacketSent_cell p).wp (fun t => t = s)
  have h_send := fun p bytes => (sendBufferToPeer_cell p bytes).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, sendHandshakeResponse, h_gp, h_sp, h_create, h_mac, h_begin, h_session, h_trav, h_sent, h_send, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem setPeerEndpointFromSkb_cell pid src : SameView nativeCell (setPeerEndpointFromSkb pid src) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_ep := fun src => (kernel (endpointFromSkb_sameWGStore src)).wp (fun t => t = s)
  have h_set := fun p e => (setPeerEndpoint_cell p e).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, setPeerEndpointFromSkb, h_ep, h_set, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem sendKeepalive_cell pid : SameView nativeCell (sendKeepalive pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_send := fun p => (sendStagedPackets_cell p).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, sendKeepalive, getDev, h_gp, h_sp, h_send, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem cookieMessageConsume_cell msg : SameView nativeCell (cookieMessageConsume msg) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_put := fun id => (peerPut_frame id).wp (fun t => t = s)
  have h_lookup := fun ks i => (indexLookup_frame ks i).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, cookieMessageConsume, h_gp, h_sp, h_put, h_lookup, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem sendBufferAsReplyToSkb_cell src bytes : SameView nativeCell (sendBufferAsReplyToSkb src bytes) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_ep := fun src => (kernel (endpointFromSkb_sameWGStore src)).wp (fun t => t = s)
  have h_four := fun e => (send4_cell e none bytes 0 false).wp (fun t => t = s)
  have h_six := fun e => (send6_cell e none bytes 0 false).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, sendBufferAsReplyToSkb, h_ep, h_four, h_six, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem sendHandshakeCookie_cell msg src : SameView nativeCell (sendHandshakeCookie msg src) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_cookie := fun i src mac => (cookie_native_frame (cookieMessageCreate_sameCookie i src mac)).wp (fun t => t = s)
  have h_send := fun src bytes => (sendBufferAsReplyToSkb_cell src bytes).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, sendHandshakeCookie, h_cookie, h_send, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

private theorem afterMac_cell msg src loaded mac : SameView nativeCell (Cookies.afterMac msg src loaded mac) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_put := fun id => (peerPut_frame id).wp (fun t => t = s)
  have h_sendcookie := fun msg src => (sendHandshakeCookie_cell msg src).wp (fun t => t = s)
  have h_init := fun msg => (consumeInitiation_cell msg).wp (fun t => t = s)
  have h_resp := fun msg => (consumeResponse_cell msg).wp (fun t => t = s)
  have h_ep := fun p src => (setPeerEndpointFromSkb_cell p src).wp (fun t => t = s)
  have h_send := fun p => (sendHandshakeResponse_cell p).wp (fun t => t = s)
  have h_begin := fun p => (beginSession_cell p).wp (fun t => t = s)
  have h_derived := fun p => (timersSessionDerived_cell p).wp (fun t => t = s)
  have h_complete := fun p => (timersHandshakeComplete_cell p .walltimeLastHandshake).wp (fun t => t = s)
  have h_keep := fun p => (sendKeepalive_cell p).wp (fun t => t = s)
  have h_recv := fun p => (timersAnyAuthenticatedPacketReceived_cell p).wp (fun t => t = s)
  have h_trav := fun p => (timersTraversal_cell p).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, Cookies.afterMac, getDev, modifyDev, h_gp, h_sp, h_put, h_sendcookie, h_init, h_resp, h_ep, h_send, h_begin, h_derived, h_complete, h_keep, h_recv, h_trav, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem receiveHandshakePacket_cell msg src : SameView nativeCell (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have hc := (cookieMessageConsume_cell msg).wp (fun t => t = s)
  have hl := (kernel Cookies.loadPhase_sameStore).wp (fun t => t = s)
  have hv := fun loaded => (cookie_native_frame (cookieValidatePacket_sameCookie msg src loaded)).wp (fun t => t = s)
  have ha := fun loaded mac => (afterMac_cell msg src loaded mac).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, hiddenClock64,
    branch, branchCmp, invariant, hc, hl, hv, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem receiveStep_cell  : SameView nativeCell (receiveStep) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have table {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d ix hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient table
  have h_recv := fun msg src => (receiveHandshakePacket_cell msg src).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, table, hidden, hiddenClock64, hiddenAlloc, receiveStep, getDev, modifyDev, h_recv, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

end Leanux.Proofs.WG.Queues.RxRing
