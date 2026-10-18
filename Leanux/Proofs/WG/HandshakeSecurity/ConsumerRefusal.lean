import Leanux.Proofs.WG.HandshakeSecurity.RefusalClaims

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

private theorem from_native {α : Type} (action : WG.M α)
    (frame : ∀ w a x v b, (action.run w).run a = .ok ((x, v), b) → RetainsHandshake w v)
    (initial : WGWorld) : Preserves (RetainsHandshake initial) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact hi.trans (frame w a x v b run)

private theorem getDev_frame (initial : WGWorld) : Preserves (RetainsHandshake initial) getDev := by
  apply from_native
  intro w a x v b run
  cases hd : w.dev with
  | none =>
    simp [getDev, hd, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    simp [getDev, hd] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact .refl _

private theorem getPeer_frame (pid : PeerId) (initial : WGWorld) :
    Preserves (RetainsHandshake initial) (getPeer pid) := by
  apply from_native
  intro w a p v b run
  rw [(Queues.getPeer_normal pid w v p a b run).1]
  exact .refl _

private theorem chain {α β : Type} (initial : WGWorld) (action : WG.M α)
    (next : α → WG.M β) (post : β → WGWorld → Prop)
    (first : Preserves (RetainsHandshake initial) action)
    (tail : ∀ x, Hoare (next x) (RetainsHandshake initial) post) :
    Hoare (action >>= next) (RetainsHandshake initial) post :=
  hoare_bind action next first tail

private def Refused (initial : WGWorld) (result : Option PeerId) (w : WGWorld) : Prop :=
  result = none → RetainsHandshake initial w

private theorem out_rule (peer : Option PeerId) (initial : WGWorld) :
    Hoare (Queues.RxCredits.HandshakeLoans.initiationOut peer none)
      (RetainsHandshake initial) (Refused initial) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run _
  exact hi.trans (out_none_retains peer w v a b result run)

private theorem checked_rule (msg e ck hash t : List UInt8) (peer : Option PeerId)
    (pid : PeerId) (p : Peer) (initial : WGWorld) :
    Hoare (checkedWith (fun a => a) timestampStep msg e ck hash t peer pid p)
      (RetainsHandshake initial) (Refused initial) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run none
  subst result
  exact hi.trans (checked_none_retains msg e ck hash t peer pid p w v a b run)

theorem consume_refusal (msg : List UInt8) (initial : WGWorld) :
    Hoare (consumeInitiation msg) (RetainsHandshake initial) (Refused initial) := by
  have ambient {α : Type} (action : AmbientM α) :
      Preserves (RetainsHandshake initial) (monadLift action : WG.M α) :=
    hoare_liftAmbient action _
  have lookup (key : Key) : Preserves (RetainsHandshake initial) (pubkeyLookup key) :=
    from_native _ (fun w a result v b run => pubkeyLookup_retains_handshake key w v a b result run) initial
  have stop (message : String) : Hoare (invariant message : WG.M (Option PeerId))
      (RetainsHandshake initial) (Refused initial) := by
    exact hoare_consequence (ambient (AmbientM.invariant message))
      (fun _ h => h) (fun _ _ h _ => h)
  have ephemeral (copy : Bool) (e ck hash : List UInt8) :
      Preserves (RetainsHandshake initial) (messageEphemeral copy e ck hash) :=
    (messageEphemeral_sameWGWorld copy e ck hash).wp (RetainsHandshake initial)
  have dh (flag : Bool) (ck privateKey publicKey : List UInt8) :
      Preserves (RetainsHandshake initial) (mixDh flag ck privateKey publicKey) :=
    (mixDh_sameWGWorld flag ck privateKey publicKey).wp (RetainsHandshake initial)
  have precomputed (ck key : List UInt8) :
      Preserves (RetainsHandshake initial) (mixPrecomputedDh ck key) :=
    (mixPrecomputedDh_sameWGWorld ck key).wp (RetainsHandshake initial)
  have decrypt (msg key hash : List UInt8) :
      Preserves (RetainsHandshake initial) (messageDecrypt msg key hash) :=
    (messageDecrypt_sameWGWorld msg key hash).wp (RetainsHandshake initial)
  rw [← consume_factor]
  unfold consumeWith
  repeat' first
    | with_reducible exact checked_rule _ _ _ _ _ _ _ _ initial
    | with_reducible exact out_rule _ initial
    | with_reducible exact stop _
    | with_reducible exact getDev_frame initial
    | with_reducible exact getPeer_frame _ initial
    | with_reducible exact lookup _
    | with_reducible exact ephemeral _ _ _ _
    | with_reducible exact dh _ _ _ _
    | with_reducible exact precomputed _ _
    | with_reducible exact decrypt _ _ _
    | with_reducible exact ambient _
    | with_reducible apply chain initial
    | (session_origin_intro_forall; try dsimp only)
    | split
    | unfold branch

theorem original_none_retains (msg : List UInt8) (w v : WGWorld) (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a = .ok ((none, v), b)) :
    RetainsHandshake w v :=
  (hoare_iff_run_ambient _ _ _).mp (consume_refusal msg w) w a none v b (.refl _) run rfl

end Leanux.Proofs.WG.HandshakeSecurity
