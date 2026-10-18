import Leanux.Proofs.WG.Roaming.RemotePeerFrames
import Leanux.Proofs.WG.Index.ResponseIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing TimerDiscipline Std.Do

theorem creatorPublish_remotes (pid : PeerId) : SameView destinationAt (Index.creatorPublish pid) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  let P := fun g => destinationAt g = entry
  unfold Index.creatorPublish
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (indexOwner_peerDeref_preserves (.handshake pid) P)) ?_
  intro _ g ambient value final after pre run
  cases device : g.dev with
  | none =>
    rw [liftIndex_run_variant,device] at run
    cases run
  | some d =>
    obtain ⟨ending,_⟩ := Index.indexInsert_exact (.handshake pid) d
      g ambient value final after device run
    change destinationAt final = entry
    have same : destinationAt final = destinationAt g := by
      funext target
      simp [destinationAt,peerAt,ending,device]
    exact same.trans pre

theorem createResponse_remotes (pid : PeerId) : SameView destinationAt (createResponse pid) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  exact Index.createResponse_preserves_source pid (fun g => destinationAt g = entry)
    (fun ck hash => (ensures_iff _ _ _).mpr
      (modifyPeer_remotes pid (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl) entry))
    (fun secret => (ensures_iff _ _ _).mpr
      (modifyPeer_remotes pid (fun p => {p with ephemeralPrivate := clamp secret}) (fun _ => rfl) entry))
    ((ensures_iff _ _ _).mpr
      (modifyPeer_remotes pid (fun p => {p with handshakeState := HANDSHAKE_CREATED_RESPONSE})
        (fun _ => rfl) entry))
    ((ensures_iff _ _ _).mpr (creatorPublish_remotes pid entry))

theorem addMacToPacket_spec_remotes_variant (pid : PeerId) (msg : List UInt8) :
    SameView destinationAt (addMacToPacket pid msg) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  let P : WGWorld → Prop := fun g => destinationAt g = entry
  have test (p : Peer) :
      Ensures (WG.andM (branch .addMacCookieValid p.cookieIsValid)
        (branchExpired .addMacCookieFresh p.cookieBirthdate COOKIE_FRESH_SECONDS (!·)))
        P (fun _ => P) := by
    apply (ensures_iff _ P (fun _ => P)).mpr
    exact DumpComposition.andM_sameView _ _
      (fun initial => hoare_liftAmbient (AmbientM.branch .addMacCookieValid p.cookieIsValid)
        (fun g => destinationAt g = initial))
      ((branchExpired_sameWGWorld _ _ _ (!·)).factor destinationAt) entry
  unfold addMacToPacket
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
  intro p
  dsimp only
  refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_)
  · intro g a result final after pre run
    cases run
    apply Eq.trans _ pre.1
    funext target
    cases device : g.dev with
    | none => simp [peerAt,device] at pre
    | some d =>
      have resident : d.peers[pid]? = some p := by simpa [peerAt,device] using pre.2
      by_cases same : pid = target
      · subst target
        simp [destinationAt,peerAt,device,resident]
      · simp [destinationAt,peerAt,device,Std.TreeMap.getElem?_insert,same]
  · refine ensures_bind _ _ (test p) ?_
    intro accepted
    split <;> (intro g a result final after pre run; cases run; exact pre)

end Leanux.Proofs.WG.Roaming
