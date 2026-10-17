import Leanux.Proofs.WG.Noise.AccessSource
import Leanux.Proofs.WG.Noise.CryptoFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do

/-- Local variant of Keypairs.Frames.WGTransitions.createResponse_spec.
Response construction changes handshake/index data, but not the allocation
serial. This includes all normal refusals on arbitrary native inputs. -/
theorem createResponse_spec_counter_variant (pid : PeerId) (counter : Nat) :
    Noise.Ensures (createResponse pid) (fun g => g.keypairCounter = counter)
      (fun _ g => g.keypairCounter = counter) := by
  let P : WGWorld → Prop := fun g => g.keypairCounter = counter
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient value final after pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (site : Decision) (b : Bool) : Ensures (branch site b : WG.M Bool) P (fun _ => P) :=
    hambient (AmbientM.branch site b)
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient value final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient value final after pre run).1
  have hset (p : Peer) : Ensures (setPeer pid p) P (fun _ => P) := by
    intro g ambient value final after pre run; cases run; exact pre
  have hwrite (f : Peer → Peer) : Ensures (do setPeer pid (f (← getPeer pid))) P (fun _ => P) :=
    ensures_bind _ _ hread (fun p => hset (f p))
  have hchain (ck hash : List UInt8) :
      Ensures ((noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash) P (fun _ => P) :=
    hwrite (fun p => {p with chainingKey := ck, hash})
  have hderef : Ensures (IndexOwner.peerDeref (.handshake pid)) P (fun _ => P) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind _ _ (ensures_bind _ _ hread (fun p => hpure p.handshakeEntryPeer)) ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported "entry->peer is NULL: the C dereferences it")
    | some target => exact hpure target
  have hindex : Ensures (liftIndex (indexInsert (.handshake pid))) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ P (by intro g d table pre device; exact pre))
  change Ensures _ P (fun _ => P)
  unfold createResponse
  refine ensures_bind _ _ hread ?_
  intro p
  refine ensures_bind _ _ (hbranch _ _) ?_
  intro refused
  cases refused with
  | true => exact hpure none
  | false =>
    refine ensures_bind _ _ (hambient (AmbientM.hidden .respEphemeral)) ?_
    intro secret
    rw [← bind_assoc]
    refine ensures_bind _ _ (hwrite (fun p => {p with ephemeralPrivate := clamp secret})) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (generatePublic_wg_spec P _)) ?_
    intro generated
    obtain ⟨pub,ok⟩ := generated
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro noEphemeral
    cases noEphemeral with
    | true => exact hpure none
    | false =>
      cases pub with
      | none => exact hambient (AmbientM.invariant "unreachable")
      | some e =>
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (messageEphemeral_wg_spec P _ _ _ _)) ?_
        intro ephemeral
        obtain ⟨ck,hash⟩ := ephemeral
        refine ensures_bind _ _ (hchain _ _) ?_
        intro _
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixDh_wg_spec P _ _ _ _)) ?_
        intro ee
        refine ensures_bind _ _ (hbranch _ _) ?_
        intro failed
        cases failed with
        | true => exact hpure none
        | false =>
          cases ee with
          | none => exact hambient (AmbientM.invariant "unreachable")
          | some pair =>
            obtain ⟨ck,key⟩ := pair
            refine ensures_bind _ _ (hchain _ _) ?_
            intro _
            refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixDh_wg_spec P _ _ _ _)) ?_
            intro se
            refine ensures_bind _ _ (hbranch _ _) ?_
            intro failed
            cases failed with
            | true => exact hpure none
            | false =>
              cases se with
              | none => exact hambient (AmbientM.invariant "unreachable")
              | some pair =>
                obtain ⟨ck,key⟩ := pair
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdf_wg_spec P _ _ _ _)) ?_
                intro outs
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 0)) ?_
                intro ck
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 1)) ?_
                intro tempHash
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 2)) ?_
                intro key
                refine ensures_bind _ _ (hchain _ _) ?_
                intro _
                refine ensures_bind _ _ hderef ?_
                intro _
                refine ensures_bind _ _ hindex ?_
                intro index
                rw [← bind_assoc]
                exact ensures_bind _ _ (hwrite (fun p => {p with handshakeState := HANDSHAKE_CREATED_RESPONSE}))
                  (fun _ => hpure _)

/-- Local variant of Keypairs.Frames.WGTransitions.addMacToPacket_spec.
MAC publication and its optional freshness clock preserve the allocation
serial on every normal return, without assuming a valid cookie or resident peer. -/
theorem addMacToPacket_spec_counter_variant (pid : PeerId) (msg : List UInt8) (counter : Nat) :
    Noise.Ensures (addMacToPacket pid msg) (fun g => g.keypairCounter = counter)
      (fun _ g => g.keypairCounter = counter) := by
  let P : WGWorld → Prop := fun g => g.keypairCounter = counter
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient value final after pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient value final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient value final after pre run).1
  have hset (p : Peer) : Ensures (setPeer pid p) P (fun _ => P) := by
    intro g ambient value final after pre run; cases run; exact pre
  have hexpired (birthday : Int64) :
      Ensures (branchExpired .addMacCookieFresh birthday COOKIE_FRESH_SECONDS (!·)) P (fun _ => P) := by
    unfold branchExpired birthdateTest
    rw [bind_assoc]
    refine ensures_bind _ _ (hambient (AmbientM.hiddenClock64 .birthdateExpired)) ?_
    intro now
    simp only [pure_bind]
    exact hambient (AmbientM.branchCmp _ _ _ _)
  change Ensures _ P (fun _ => P)
  unfold addMacToPacket
  refine ensures_bind _ _ hread ?_
  intro p
  refine ensures_bind _ _ (hset _) ?_
  intro _
  refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
  · unfold Leanux.WG.andM
    refine ensures_bind _ _ (hambient (AmbientM.branch .addMacCookieValid p.cookieIsValid)) ?_
    intro valid
    cases valid with
    | false => exact hpure false
    | true => exact hexpired _
  · intro valid
    cases valid <;> exact hpure _

end Leanux.Proofs.WG.TimerDiscipline
