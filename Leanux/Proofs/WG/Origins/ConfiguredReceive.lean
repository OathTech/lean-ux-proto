import Leanux.Proofs.WG.Origins.ConfiguredHandshake
import Leanux.Proofs.WG.Origins.CurrentIndex

/-! Concrete native Noise receive contracts. Failed authentication may pay and
erase a peer; normal returns retain configured and current identity invariants.
These statements do not assert an endpoint for a Stop. -/
namespace Leanux.Proofs.WG.ConfiguredReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues
open Leanux.Proofs.WG.ConfiguredIdentity Leanux.Proofs.WG.ConfiguredHandshake

/-- Constructing a response only edits unobserved handshake fields and index
entries; nullable owner resolution and every cryptographic branch remain actual. -/
theorem createResponse_view (pid : PeerId) : SameView view (createResponse pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first
    | (rx_retention_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp (fun w => view w = initial))
    | (rx_retention_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp (fun w => view w = initial))
    | configured_crypto initial
    | configured_step initial

theorem createResponse_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (createResponse pid) :=
  ConfiguredHandshake.current_preserves _ (createResponse_view pid)
    (Origins.Retaining.of_view (Origins.Retaining.createResponse_material pid)) history

theorem pubkeyLookup_view (key : Key) : SameView view (pubkeyLookup key) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero
       exact (peerGetMaybeZero_view _).wp (fun s => s = initial))
    | configured_step initial

private theorem update_peer (history : List SessionOrigin.Receipt) (pid : PeerId) (f : Peer → Peer)
    (hf : ∀ p, cell (f p) = cell p) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (getPeer pid >>= fun p => setPeer pid (f p)) :=
  ConfiguredHandshake.current_preserves _ (ConfiguredIdentity.modifyPeer_view pid f hf)
    (Origins.Retaining.of_view (SameView.bind (Origins.getPeer_view pid)
      (fun p => Origins.setPeer_view pid (f p)))) history

private theorem update_peer_bind {α : Type} (history : List SessionOrigin.Receipt)
    (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (hf : ∀ p, cell (f p) = cell p)
    (ht : ∀ x, Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w) (tail x)) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  have h := preserves_bind (update_peer history pid f hf) ht
  simpa only [bind_assoc] using h

open Lean Meta Elab Tactic in
/-- Select only an actual fresh read immediately followed by its setter. -/
elab "receive_update_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Preserves do throwError "not a preservation contract"
  let .app _ action := target | throwError "missing action"
  let action := action.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let args := action.getAppArgs
  unless args.size ≥ 2 do throwError "missing bind arguments"
  let first := args[args.size-2]!.consumeMData
  unless first.isAppOf ``getPeer do throwError "not a peer getter"
  let .lam _ _ body _ := args.back!.consumeMData | throwError "not an explicit continuation"
  let body := body.consumeMData
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  unless body.isAppOf expected do throwError "different continuation head"
  if expected == ``Bind.bind then
    let next := body.getAppArgs
    unless next.size ≥ 2 do throwError "missing write bind arguments"
    unless next[next.size-2]!.consumeMData.isAppOf ``setPeer do
      throwError "the next action is not the peer setter"

private theorem getPeer_preserves (P : WGWorld → Prop) (pid : PeerId) : Preserves P (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hi hr
  rw [(Peers.getPeer_current pid w v p ambient ambient' hr).1]
  exact hi

macro "receive_crypto " P:term : tactic => `(tactic| first
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp $P)
  | (rx_retention_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp $P)
  | (rx_retention_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp $P)
  | (rx_retention_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp $P)
  | (rx_retention_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp $P)
  | (rx_retention_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp $P)
  | (rx_retention_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp $P))

private theorem preserve_ite {α : Type} (c : Prop) [Decidable c]
    (a b : WG.M α) (P : WGWorld → Prop)
    (ha : Preserves P a) (hb : Preserves P b) : Preserves P (if c then a else b) := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using ha
  · simpa only [ite_eq_right hc] using hb

macro "receive_basic " history:term " with " P:term : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply update_peer $history
     intro p; rfl)
  | (receive_update_head Bind.bind
     apply update_peer_bind $history
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact getPeer_preserves $P _)
  | (rx_retention_head getDev; unfold getDev)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ $P)
  | (rx_retention_head get; exact hoare_consequence (hoare_get $P)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get; exact hoare_consequence (hoare_get $P)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) $P)
  | (rx_retention_head ite; apply preserve_ite)
  | rx_retention_step)

private theorem peerPut_preserves (history : List SessionOrigin.Receipt) (peer : Option PeerId) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w) (peerPut peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.peerPut_preserves peer)
      w ambient result v ambient' hi.1 hr,
    hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp
      (CurrentIdentity.peerPut_retains peer) w ambient result v ambient' hr)⟩

theorem consumeInitiation_preserves (msg : List UInt8) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (consumeInitiation msg) := by
  let P := fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w
  change Preserves P _
  have lookup (key : Key) : Preserves P (pubkeyLookup key) :=
    ConfiguredHandshake.current_preserves _ (pubkeyLookup_view key)
      (Origins.Retaining.of_view (Origins.Retaining.pubkeyLookup_material key)) history
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head pubkeyLookup; exact lookup _)
    | (rx_retention_head peerPut; exact peerPut_preserves history _)
    | receive_crypto P
    | receive_basic history with P

theorem consumeResponse_preserves (msg : List UInt8) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (consumeResponse msg) := by
  let P := fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w
  change Preserves P _
  have lookup (kinds : List IndexKind) (index : Nat) : Preserves P (indexLookup kinds index) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hi hr
    exact ⟨(hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.indexLookup_preserves kinds index)
        w ambient result v ambient' hi.1 hr,
      hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp
        (CurrentIdentity.indexLookup_current kinds index) w ambient result v ambient' hr)⟩
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact lookup _ _)
    | (rx_retention_head peerPut; exact peerPut_preserves history _)
    | receive_crypto P
    | receive_basic history with P

end Leanux.Proofs.WG.ConfiguredReceive
