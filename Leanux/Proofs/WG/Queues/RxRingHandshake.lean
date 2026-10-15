import Leanux.Proofs.WG.Queues.RxRingTx

/-! The handshake worker never admits transport data. These concrete full
RX-cell frames cover its cookie, Noise, session, reply and TX-staging callees.
Malformed types and every original Stop remain executable source outcomes. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem indexInsert_cell owner : SameView cell (indexInsert owner) := by
  intro w x v hr
  have he := indexInsert_sameIndexKernel owner w x v hr
  have h := congrArg (fun k : Kernel => k.wg.map fun d => (d.ifindex, d.decryptQueue)) he
  simpa [indexKernelView, indexKernel, cell, Option.map_map, Function.comp_def] using h

theorem cookie_frame (ha : SameCookieKernel a) : SameView cell a := by
  intro w x v hr
  have h := congrArg (fun k : Kernel => k.wg.map fun d => (d.ifindex, d.decryptQueue)) (ha w x v hr)
  simpa [cookieKernelView, cookieKernel, cookieDevice, cell, Option.map_map, Function.comp_def] using h

theorem pubkeyLookup_cell key : SameView cell (pubkeyLookup key) := by
  apply SameView.of_wp
  intro s
  have h_pg := fun id => (peerGetMaybeZero_frame id).wp (fun t => t = s)
  mvcgen [pubkeyLookup, getDev, getK, h_pg, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem consumeInitiation_cell msg : SameView cell (consumeInitiation msg) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_put := fun id => (peerPut_frame id).wp (fun t => t = s)
  have h_clock := fun site => (kernel (hiddenClock64_sameKernel site)).wp (fun t => t = s)
  have h_eph := fun b e ck h => (kernel (messageEphemeral_sameKernel b e ck h)).wp (fun t => t = s)
  have h_dh := fun b ck p q => (kernel (mixDh_sameKernel b ck p q)).wp (fun t => t = s)
  have h_pre := fun ck p => (kernel (mixPrecomputedDh_sameKernel ck p)).wp (fun t => t = s)
  have h_dec := fun a k h => (kernel (messageDecrypt_sameKernel a k h)).wp (fun t => t = s)
  have h_look := fun k => (pubkeyLookup_cell k).wp (fun t => t = s)
  have h_b := fun d v => (kernel (sameKernel_branch d v)).wp (fun t => t = s)
  have h_bc := fun d v a b => (kernel (branchCmp_sameKernel d v a b)).wp (fun t => t = s)
  mvcgen [h_b, h_bc, consumeInitiation, getDev, getK, h_gp, h_sp, h_put, h_clock, h_eph, h_dh, h_pre, h_dec, h_look, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem consumeResponse_cell msg : SameView cell (consumeResponse msg) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_put := fun id => (peerPut_frame id).wp (fun t => t = s)
  have h_lookup := fun ks i => (indexLookup_frame ks i).wp (fun t => t = s)
  have h_eph := fun b e ck h => (kernel (messageEphemeral_sameKernel b e ck h)).wp (fun t => t = s)
  have h_dh := fun b ck p q => (kernel (mixDh_sameKernel b ck p q)).wp (fun t => t = s)
  have h_dec := fun a k h => (kernel (messageDecrypt_sameKernel a k h)).wp (fun t => t = s)
  have h_kdf := fun b c ck d => (kernel (Framing.kdf_sameKernel b c ck d)).wp (fun t => t = s)
  have h_out := fun xs i => (kernel (Framing.kdfOut_sameKernel xs i)).wp (fun t => t = s)
  mvcgen [consumeResponse, getDev, getK, h_gp, h_sp, h_put, h_lookup, h_eph, h_dh, h_dec, h_kdf, h_out, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem createResponse_cell pid : SameView cell (createResponse pid) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_hidden := fun site => (kernel (hidden_sameKernel site)).wp (fun t => t = s)
  have h_pub := fun k => (kernel (generatePublic_sameKernel k)).wp (fun t => t = s)
  have h_eph := fun b e ck h => (kernel (messageEphemeral_sameKernel b e ck h)).wp (fun t => t = s)
  have h_dh := fun b ck p q => (kernel (mixDh_sameKernel b ck p q)).wp (fun t => t = s)
  have h_kdf := fun b c ck d => (kernel (Framing.kdf_sameKernel b c ck d)).wp (fun t => t = s)
  have h_out := fun xs i => (kernel (Framing.kdfOut_sameKernel xs i)).wp (fun t => t = s)
  have h_idx := fun owner => (indexInsert_cell owner).wp (fun t => t = s)
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  have h_owner := fun o => (kernel (indexOwner_peerDeref_sameKernel o)).wp (fun t => t = s)
  have h_word := fun o => (kernel (indexOwner_peerWord_sameKernel o)).wp (fun t => t = s)
  mvcgen [h_owner, h_word, h_gp, h_sp, h_hidden, h_pub, h_eph, h_dh, h_kdf, h_out, h_idx, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem addMacToPacket_cell pid msg : SameView cell (addMacToPacket pid msg) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_exp := fun d b n f => (kernel (branchExpired_sameKernel d b n f)).wp (fun t => t = s)
  mvcgen [addMacToPacket, h_gp, h_sp, h_exp, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem keypairCreate_cell pid : SameView cell (keypairCreate pid) := by
  apply SameView.of_wp
  intro s
  have h_alloc := fun site => (kernel (hiddenAlloc_sameKernel site)).wp (fun t => t = s)
  have h_sk := fun id k => (setKeypair_cell id k).wp (fun t => t = s)
  mvcgen [keypairCreate, getDev, getK, modifyDev, modifyK, h_alloc, h_sk, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem addNewKeypair_cell pid kp : SameView cell (addNewKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_gk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have h_kput := fun id b => (keypairPut_frame id b).wp (fun t => t = s)
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  mvcgen [h_gp, h_sp, h_gk, h_kput, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem deriveKeys_cell kp initiator ck : SameView cell (deriveKeys kp initiator ck) := by
  apply SameView.of_wp
  intro s
  have h_gk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have h_sk := fun id k => (setKeypair_cell id k).wp (fun t => t = s)
  have h_clock := fun site => (kernel (hiddenClock64_sameKernel site)).wp (fun t => t = s)
  have h_kdf := fun b c ck d => (kernel (Framing.kdf_sameKernel b c ck d)).wp (fun t => t = s)
  have h_out := fun xs i => (kernel (Framing.kdfOut_sameKernel xs i)).wp (fun t => t = s)
  mvcgen [deriveKeys, h_gk, h_sk, h_clock, h_kdf, h_out, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem handshakeZero_cell pid : SameView cell (handshakeZero pid) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  mvcgen [handshakeZero, h_gp, h_sp, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem indexReplaceHandshake_cell pid kp : SameView cell (indexReplaceHandshake pid kp) := by
  apply SameView.of_wp
  intro s
  mvcgen [indexReplaceHandshake, indexHashed, getDev, getK, modifyDev, modifyK, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem beginSession_cell pid : SameView cell (beginSession pid) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_gk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have h_sk := fun id k => (setKeypair_cell id k).wp (fun t => t = s)
  have h_create := fun p => (keypairCreate_cell p).wp (fun t => t = s)
  have h_derive := fun k b ck => (deriveKeys_cell k b ck).wp (fun t => t = s)
  have h_zero := fun p => (handshakeZero_cell p).wp (fun t => t = s)
  have h_add := fun p k => (addNewKeypair_cell p k).wp (fun t => t = s)
  have h_replace := fun p k => (indexReplaceHandshake_cell p k).wp (fun t => t = s)
  have h_owner := fun o => (kernel (indexOwner_peerDeref_sameKernel o)).wp (fun t => t = s)
  have h_word := fun o => (kernel (indexOwner_peerWord_sameKernel o)).wp (fun t => t = s)
  mvcgen [h_owner, h_word, beginSession, h_gp, h_sp, h_gk, h_sk, h_create, h_derive, h_zero, h_add, h_replace, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem timersSessionDerived_cell pid : SameView cell (timersSessionDerived pid) := by
  apply SameView.of_wp
  intro s
  have h_mod := fun site p t n => (modPeerTimer_cell site p t n).wp (fun t => t = s)
  have hd (α : Type) := discard_view_spec cell (α := α) (fun t => t = s)
  mvcgen [timersSessionDerived, h_mod, hd]

theorem sendBufferToPeer_cell pid bytes : SameView cell (sendBufferToPeer pid bytes) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_alloc := fun site => (kernel (hiddenAlloc_sameKernel site)).wp (fun t => t = s)
  have h_four := fun e => (send4_cell e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  have h_six := fun e => (send6_cell e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  mvcgen [sendBufferToPeer, h_gp, h_sp, h_alloc, h_four, h_six, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem sendHandshakeResponse_cell pid : SameView cell (sendHandshakeResponse pid) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_clock := fun site => (kernel (hiddenClock64_sameKernel site)).wp (fun t => t = s)
  have h_create := fun p => (createResponse_cell p).wp (fun t => t = s)
  have h_mac := fun p msg => (addMacToPacket_cell p msg).wp (fun t => t = s)
  have h_begin := fun p => (beginSession_cell p).wp (fun t => t = s)
  have h_session := fun p => (timersSessionDerived_cell p).wp (fun t => t = s)
  have h_trav := fun p => (timersTraversal_cell p).wp (fun t => t = s)
  have h_sent := fun p => (timersAnyAuthenticatedPacketSent_cell p).wp (fun t => t = s)
  have h_send := fun p bytes => (sendBufferToPeer_cell p bytes).wp (fun t => t = s)
  mvcgen [sendHandshakeResponse, h_gp, h_sp, h_clock, h_create, h_mac, h_begin, h_session, h_trav, h_sent, h_send, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem setPeerEndpointFromSkb_cell pid src : SameView cell (setPeerEndpointFromSkb pid src) := by
  apply SameView.of_wp
  intro s
  have h_ep := fun src => (kernel (endpointFromSkb_sameKernel src)).wp (fun t => t = s)
  have h_set := fun p e => (setPeerEndpoint_cell p e).wp (fun t => t = s)
  mvcgen [setPeerEndpointFromSkb, h_ep, h_set, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem sendKeepalive_cell pid : SameView cell (sendKeepalive pid) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_alloc := fun site => (kernel (hiddenAlloc_sameKernel site)).wp (fun t => t = s)
  have h_send := fun p => (sendStagedPackets_cell p).wp (fun t => t = s)
  mvcgen [sendKeepalive, getDev, getK, h_gp, h_sp, h_alloc, h_send, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem cookieMessageConsume_cell msg : SameView cell (cookieMessageConsume msg) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_put := fun id => (peerPut_frame id).wp (fun t => t = s)
  have h_lookup := fun ks i => (indexLookup_frame ks i).wp (fun t => t = s)
  have h_clock := fun site => (kernel (hiddenClock64_sameKernel site)).wp (fun t => t = s)
  mvcgen [cookieMessageConsume, h_gp, h_sp, h_put, h_lookup, h_clock, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem sendBufferAsReplyToSkb_cell src bytes : SameView cell (sendBufferAsReplyToSkb src bytes) := by
  apply SameView.of_wp
  intro s
  have h_alloc := fun site => (kernel (hiddenAlloc_sameKernel site)).wp (fun t => t = s)
  have h_ep := fun src => (kernel (endpointFromSkb_sameKernel src)).wp (fun t => t = s)
  have h_four := fun e => (send4_cell e none bytes 0 false).wp (fun t => t = s)
  have h_six := fun e => (send6_cell e none bytes 0 false).wp (fun t => t = s)
  mvcgen [sendBufferAsReplyToSkb, h_alloc, h_ep, h_four, h_six, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem sendHandshakeCookie_cell msg src : SameView cell (sendHandshakeCookie msg src) := by
  apply SameView.of_wp
  intro s
  have h_cookie := fun i src mac => (cookie_frame (cookieMessageCreate_sameCookieKernel i src mac)).wp (fun t => t = s)
  have h_send := fun src bytes => (sendBufferAsReplyToSkb_cell src bytes).wp (fun t => t = s)
  mvcgen [sendHandshakeCookie, h_cookie, h_send, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem receiveHandshakePacket_cell msg src : SameView cell (receiveHandshakePacket msg src) := by
  apply SameView.of_wp
  intro s
  have h_gp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have h_sp := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have h_put := fun id => (peerPut_frame id).wp (fun t => t = s)
  have h_clock := fun site => (kernel (hiddenClock64_sameKernel site)).wp (fun t => t = s)
  have h_cookie := fun msg => (cookieMessageConsume_cell msg).wp (fun t => t = s)
  have h_age := fun b n => (kernel (birthdateTest_sameKernel b n)).wp (fun t => t = s)
  have h_val := fun msg src b => (cookie_frame (cookieValidatePacket_sameCookieKernel msg src b)).wp (fun t => t = s)
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
  mvcgen [receiveHandshakePacket, getDev, getK, modifyDev, modifyK, h_gp, h_sp, h_put, h_clock, h_cookie, h_age, h_val, h_sendcookie, h_init, h_resp, h_ep, h_send, h_begin, h_derived, h_complete, h_keep, h_recv, h_trav, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem receiveStep_cell  : SameView cell (receiveStep) := by
  apply SameView.of_wp
  intro s
  have h_recv := fun msg src => (receiveHandshakePacket_cell msg src).wp (fun t => t = s)
  mvcgen [receiveStep, getDev, getK, modifyDev, modifyK, h_recv, branch, branchCmp, WG.andM, WG.orM, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

end Leanux.Proofs.WG.Queues.RxRing
