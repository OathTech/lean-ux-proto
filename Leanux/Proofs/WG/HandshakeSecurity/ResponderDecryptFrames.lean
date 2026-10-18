import Leanux.Proofs.WG.HandshakeSecurity.ResponderGlobalFrames
import Leanux.Proofs.WG.Queues.CurrentSlotWorkers
import Leanux.Proofs.WG.Queues.DecryptCarrier

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Origins Origins.Retaining Lifetimes Queues RxCredits

theorem native_retained {a : WG.M α} (keys : CoreRetains a)
    (slots : KeyEffects NoPromotion a) (bounded : Preserves CurrentSlots.Inv a)
    (confirmed : List Nat) : Preserves (History.Native confirmed) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v b entry run
  exact ⟨entry.1.retain ((KeyEffects.iff_run_ambient _ _).mp slots w ambient result v b run)
      ((ProjectedAction.iff_run_ambient _ _ _).mp keys w ambient result v b run),
    (hoare_iff_run_ambient _ _ _).mp bounded w ambient result v b entry.2 run⟩

theorem decrypt_core (pkt : RxPacket) : SameView pool (decryptPacket pkt) := by
  intro initial
  let P := fun w => pool w = initial
  have getter (kid : KeypairId) : Preserves P (getKeypair kid) :=
    (pool_of_material (getKeypair_material kid)).wp (fun p => p = initial)
  have reject (k : Keypair) : Preserves P (KeyTimes.receiveReject k) :=
    ((decryptKeyReject_sameWGStore k).of_factor
      (fun store : WGStoreView => pool {dev := store.dev}) pool (fun _ => rfl)).wp (fun p => p = initial)
  have invalid : Preserves P (do
      let k ← getKeypair pkt.keypair
      setKeypair pkt.keypair {k with receiving := {k.receiving with isValid := false}}
      pure (none : Option RxPacket)) := by
    apply coreUpdateThen (fun p => p = initial) pkt.keypair
    · intro k; rfl
    · intro k; exact preserves_pure _
  change Preserves P _
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) P)
  intro noKey
  cases noKey with
  | true => exact preserves_pure none
  | false =>
    apply preserves_bind (getter pkt.keypair)
    intro key
    apply preserves_bind (reject key)
    intro rejected
    cases rejected with
    | true => exact invalid
    | false => exact ((Origins.receiveTail_sameWGWorld pkt key).factor pool).wp (fun p => p = initial)

theorem decrypt_native (pkt : RxPacket) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (decryptPacket pkt) := by
  apply native_retained _ _ (CurrentSlots.decryptPacket_preserves pkt) confirmed
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    rw [(ProjectedAction.iff_run_ambient _ _ _).mp (decrypt_core pkt) w a result v b run]
    exact Retains.refl _
  · exact keyEffects_view (project := id)
      ((DecryptCarrier.decryptPacket_view pkt).factor (fun v => v.1.2.2))

theorem publish_core (id : SkbId) (state : PacketState) : SameView pool (RxWorkers.publishSource id state) := by
  intro initial
  unfold RxWorkers.publishSource getRxSkb setRxSkb
  material_lower
  repeat' core_traffic (fun p => p = initial)

theorem publish_native (id : SkbId) (state : PacketState) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (RxWorkers.publishSource id state) :=
  native_fields (publish_core id state) (CurrentSlots.publish_fields id state) confirmed

theorem modify_native (f : Device → Device)
    (front : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (peers : ∀ d, (f d).peers = d.peers) (keys : ∀ d, (f d).keypairs = d.keypairs)
    (confirmed : List Nat) : Preserves (History.Native confirmed) (modifyDev f) := by
  apply native_fields
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    funext kid
    simp [pool, Option.bind_map, Function.comp_def, keys]
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotFrames.«0».Leanux.Proofs.WG.CurrentSlots.fields_modify) f front peers keys

macro "responder_native_leaf " confirmed:term : tactic => `(tactic| first
  | (rx_retention_head getRxSkb; exact History.read_native _ $confirmed)
  | (rx_retention_head setRxSkb; unfold setRxSkb; exact native_skb _ $confirmed)
  | (rx_retention_head getDev; exact native_store getDev_sameWGStore $confirmed)
  | (rx_retention_head decryptPacket; exact decrypt_native _ $confirmed)
  | (rx_retention_head RxWorkers.publishSource; exact publish_native _ _ $confirmed)
  | (rx_retention_head modifyDev
     apply modify_native
     all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

theorem prepare_native (confirmed : List Nat) :
    Preserves (History.Native confirmed) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch, invariant]
  repeat' responder_native_leaf confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
