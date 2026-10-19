import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryOriginalReleaseFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryFrames
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageEncrypt

/-! Encryption and its DEAD/CRYPTED publication retain full entry accounting.
Byte/state updates preserve immutable material; publication's paired borrow
keeps staged queues and all owning TX locations unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Encrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation Staged.Obligations

variable {history : List CausalJournal.Event} {ledger : Ledger}
variable {debts : List CleanupDebt} {locals : List TxLocalBatch}

theorem publication (items : List SkbId) (state : PacketState) :
    Preserves (Inv history ledger debts locals) (enqueuePerPeerTx items state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  cases value
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp (Admission.publication items state) w a () v b run
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp (Publication.staged items state) w a () v b run
  have core := before.core.quiet_views (v := v) [] (by simp)
    (congrArg Prod.fst material) queues (congrArg Prod.snd material)
  refine ⟨by simpa only [List.append_nil] using core,before.justified,before.allocationLinks,before.noSelected,
    (hoare_iff_run_ambient _ _ _).mp (CreateEntry.publication_bounds items state) w a () v b before.packets run,
    before.coverage.publish items state a b run,before.inventory.publish items state a b run⟩

theorem bytes (skb : SkbId) (bytes : List UInt8) :
    Preserves (Inv history ledger debts locals) (setTxSkb skb (fun p => {p with bytes})) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PacketMaterial.set_tx skb (fun p => {p with bytes}) (fun _ => rfl)) w a value v b run
  have epoch := (ProjectedAction.iff_run_ambient _ _ _).mp (PacketOrigins.skb_epoch _) w a value v b run
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp (Staged.Exact.skb _) w a value v b run
  have points := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ownershipPoints_holderStore _ (setTx_holderStore skb (fun p => {p with bytes}) (fun _ => rfl)))
    w a value v b run
  have core := before.core.quiet_views (v := v) [] (by simp) epoch queues material
  exact ⟨by simpa only [List.append_nil] using core,before.justified,before.allocationLinks,before.noSelected,
    (hoare_iff_run_ambient _ _ _).mp (Queue.mark_bounds skb _) w a value v b before.packets run,
    before.coverage.points points,before.inventory.points points⟩

theorem packet (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => Inv history ledger debts locals w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v before run
  have frame := (encrypt_packet_store key pkt).of_factor
    (fun store => StagedEntry.view {dev := store.dev}) (fun world : World => StagedEntry.view world.wg) (fun _ => rfl)
  exact before.same_view ((ProjectedAction.iff_run _ _ _).mp frame w value v run)

theorem tail (items : Option (List SkbId)) :
    Preserves (fun w : World => Inv history ledger debts locals w.wg) (RxWorkers.encryptStepTailSource items) := by
  let Q := Inv history ledger debts locals
  let P := fun w : World => Q w.wg
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : Leanux.M α) :=
    productAmbient_spec action P (fun _ _ hi => hi)
  have readNative (skb : SkbId) : Preserves Q (getTxSkb skb) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a packet v b before run
    simpa only [(Packets.getTxSkb_current skb w v packet a b run).1] using before
  have read (skb : SkbId) : Preserves P (monadLift (getTxSkb skb) : Leanux.M DataPacket) :=
    PublicationPoll.native_product Q _ (readNative skb)
  have write (skb : SkbId) (data : List UInt8) : Preserves P
      (monadLift (setTxSkb skb (fun p => {p with bytes := data})) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (bytes skb data)
  have publish (batch : List SkbId) (state : PacketState) : Preserves P
      (monadLift (enqueuePerPeerTx batch state) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (publication batch state)
  have crypt (key : KeypairId) (pkt : DataPacket) : Preserves P (encryptPacket Env.checksumHelp key pkt) := packet key pkt
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,publish,crypt,ambient]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Encrypt
