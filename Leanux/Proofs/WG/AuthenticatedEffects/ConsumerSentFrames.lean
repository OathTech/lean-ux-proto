import Leanux.Proofs.WG.AuthenticatedEffects.SentFrames
import Leanux.Proofs.Framing.WGHandshake
import Leanux.Proofs.WG.Origins.ConfiguredReceive

/-! Noise consumers never append a datagram, including their failure cleanup.
These egress frames impose no initialized-store or reference-count assumption. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem index_sent_spec (P : List SentDatagram → Prop) {α : Type} (action : IndexM α) :
    Preserves (fun w => P w.sent) (monadLift action : WG.M α) := by
  apply hoare_liftIndex
  intro w d table hi hd
  exact hi

theorem getPeer_sent_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (getPeer pid) := by
  have frame : SameView WGWorld.sent (getPeer pid) := by
    sent_frame [getPeer] using []
  exact frame.wp P

theorem setPeer_sent_spec (P : List SentDatagram → Prop) (pid : PeerId) (p : Peer) :
    Preserves (fun w => P w.sent) (setPeer pid p) := by
  apply hoare_modify
  intro w hi
  exact hi

theorem getKeypair_sent_spec (P : List SentDatagram → Prop) (id : KeypairId) :
    Preserves (fun w => P w.sent) (getKeypair id) := by
  have frame : SameView WGWorld.sent (getKeypair id) := by
    sent_frame [getKeypair] using []
  exact frame.wp P

theorem setKeypair_sent_spec (P : List SentDatagram → Prop) (id : KeypairId) (kp : Keypair) :
    Preserves (fun w => P w.sent) (setKeypair id kp) := by
  apply hoare_modify
  intro w hi
  exact hi

theorem indexRemove_sent_spec (P : List SentDatagram → Prop) (owner : IndexOwner) :
    Preserves (fun w => P w.sent) (monadLift (indexRemove owner) : WG.M Unit) :=
  index_sent_spec P _

private theorem preserve_choice {α : Type} (c : Prop) [Decidable c]
    (a b : WG.M α) (P : WGWorld → Prop)
    (ha : Preserves P a) (hb : Preserves P b) : Preserves P (if c then a else b) := by
  by_cases h : c
  · simpa only [ite_eq_left h] using ha
  · simpa only [ite_eq_right h] using hb

macro "consumer_sent_step " initial:term : tactic => `(tactic| first
  | (cookie_source_head invariant; unfold invariant)
  | (cookie_source_head getPeer; exact getPeer_sent_spec (fun s => s = $initial) _)
  | (cookie_source_head setPeer; exact setPeer_sent_spec (fun s => s = $initial) _ _)
  | (cookie_source_head getKeypair; exact getKeypair_sent_spec (fun s => s = $initial) _)
  | (cookie_source_head setKeypair; exact setKeypair_sent_spec (fun s => s = $initial) _ _)
  | (cookie_source_head getDev; unfold getDev)
  | (cookie_source_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (cookie_source_head modifyDev; apply hoare_modify; intro w hi; exact hi)
  | (cookie_source_head modify; apply hoare_modify; intro w hi; exact hi)
  | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
  | (cookie_source_lift IndexM; exact index_sent_spec (fun s => s = $initial) _)
  | (cookie_source_head ite; apply preserve_choice)
  | receive_crypto (fun w => w.sent = $initial)
  | cookie_source_step)

theorem peerPut_sent (peer : Option PeerId) : SameView WGWorld.sent (peerPut peer) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' consumer_sent_step initial

theorem peerPut_sent_spec (P : List SentDatagram → Prop) (peer : Option PeerId) :
    Preserves (fun w => P w.sent) (peerPut peer) := (peerPut_sent peer).wp P

theorem peerGetMaybeZero_sent (peer : Option PeerId) :
    SameView WGWorld.sent (peerGetMaybeZero peer) := by
  sent_frame [peerGetMaybeZero,requireNotPending,refcountIncNotZero]
    using [getPeer_sent_spec,setPeer_sent_spec]

theorem peerGetMaybeZero_sent_spec (P : List SentDatagram → Prop) (peer : Option PeerId) :
    Preserves (fun w => P w.sent) (peerGetMaybeZero peer) := (peerGetMaybeZero_sent peer).wp P

theorem pubkeyLookup_sent (key : Key) : SameView WGWorld.sent (pubkeyLookup key) := by
  sent_frame [pubkeyLookup] using [peerGetMaybeZero_sent_spec]

theorem pubkeyLookup_sent_spec (P : List SentDatagram → Prop) (key : Key) :
    Preserves (fun w => P w.sent) (pubkeyLookup key) := (pubkeyLookup_sent key).wp P

theorem messageEphemeral_sent_spec (P : List SentDatagram → Prop) (copy : Bool) (e ck hash : Key) :
    Preserves (fun w => P w.sent) (messageEphemeral copy e ck hash) :=
  ((messageEphemeral_sameWGWorld copy e ck hash).factor WGWorld.sent).wp P

theorem mixDh_sent_spec (P : List SentDatagram → Prop) (key : Bool) (ck priv pub : Key) :
    Preserves (fun w => P w.sent) (mixDh key ck priv pub) :=
  ((mixDh_sameWGWorld key ck priv pub).factor WGWorld.sent).wp P

theorem mixPrecomputedDh_sent_spec (P : List SentDatagram → Prop) (ck pre : Key) :
    Preserves (fun w => P w.sent) (mixPrecomputedDh ck pre) :=
  ((mixPrecomputedDh_sameWGWorld ck pre).factor WGWorld.sent).wp P

theorem messageDecrypt_sent_spec (P : List SentDatagram → Prop) (sealed key hash : Key) :
    Preserves (fun w => P w.sent) (messageDecrypt sealed key hash) :=
  ((messageDecrypt_sameWGWorld sealed key hash).factor WGWorld.sent).wp P

theorem consumeInitiation_sent (msg : List UInt8) : SameView WGWorld.sent (consumeInitiation msg) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (cookie_source_head Leanux.WG.pubkeyLookup; exact pubkeyLookup_sent_spec (fun s => s = initial) _)
    | (cookie_source_head Leanux.WG.peerPut; exact peerPut_sent_spec (fun s => s = initial) _)
    | consumer_sent_step initial

theorem indexLookup_sent (kinds : List IndexKind) (index : Nat) :
    SameView WGWorld.sent (indexLookup kinds index) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold indexLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (cookie_source_head IndexOwner.peerWord; unfold IndexOwner.peerWord)
    | (cookie_source_head IndexOwner.setPeerWord; unfold IndexOwner.setPeerWord)
    | (cookie_source_head peerGetMaybeZero; exact peerGetMaybeZero_sent_spec (fun s => s = initial) _)
    | (cookie_source_head ForIn.forIn
       apply list_view_spec id (fun w : WGWorld => w.sent = initial)
       intro e state
       change Preserves (fun w : WGWorld => w.sent = initial) _)
    | consumer_sent_step initial

theorem consumeResponse_sent (msg : List UInt8) : SameView WGWorld.sent (consumeResponse msg) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (cookie_source_head indexLookup; exact (indexLookup_sent _ _).wp (fun s => s = initial))
    | (cookie_source_head Leanux.WG.peerPut; exact peerPut_sent_spec (fun s => s = initial) _)
    | consumer_sent_step initial

theorem cookieMessageConsume_sent (msg : List UInt8) :
    SameView WGWorld.sent (cookieMessageConsume msg) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (cookie_source_head indexLookup; exact (indexLookup_sent _ _).wp (fun s => s = initial))
    | (cookie_source_head Leanux.WG.peerPut; exact peerPut_sent_spec (fun s => s = initial) _)
    | consumer_sent_step initial

theorem ratelimiterAllow_sent (src : SkbSource) : SameView WGWorld.sent (ratelimiterAllow src) := by
  sent_frame [ratelimiterAllow,hiddenClock] using []
  all_goals
    apply hoare_modify
    intro w hi
    dsimp only
    split <;> exact hi

theorem ratelimiterAllow_sent_spec (P : List SentDatagram → Prop) (src : SkbSource) :
    Preserves (fun w => P w.sent) (ratelimiterAllow src) := (ratelimiterAllow_sent src).wp P

theorem cookieValidatePacket_sent (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    SameView WGWorld.sent (cookieValidatePacket msg src checkCookie) := by
  sent_frame [cookieValidatePacket] using [makeCookie_sent_spec,ratelimiterAllow_sent_spec]

end Leanux.Proofs.WG.AuthenticatedEffects
