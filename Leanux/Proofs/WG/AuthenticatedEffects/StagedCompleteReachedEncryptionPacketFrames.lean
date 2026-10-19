import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionPacketSource

/-! Native packet reads, encryption and byte writes retain the same fixed
ledger. History transport uses the actual focused encryption events, separately
from the native state frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPacket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation Staged.Obligations StagedTerminalComplete
open CompleteCarrier
variable {id : SkbId}

theorem step_eq (action : Leanux.M α) : ops.step action = liftPrefix action := by
  funext w history
  change (action.run w,history ++ ((history.filterMap _).drop (history.filterMap _).length).map _) = _
  simp only [List.drop_length,List.map_nil,List.append_nil]
  rfl

theorem head_eq (id : SkbId) : ops.head id = captureRun (liftWG (getTxSkb id)) := by
  funext w history
  change runPrefix (focusPrefix _ _ (captureRun (liftWG (getTxSkb id)))) w history = _
  change ((runPrefix (captureRun (liftWG (getTxSkb id))) w
    (history.filterMap (fun event => (CausalJournal.old? event).bind Journal.encryption?))).1,
    history ++ ((runPrefix (captureRun (liftWG (getTxSkb id))) w
      (history.filterMap (fun event => (CausalJournal.old? event).bind Journal.encryption?))).2.drop
      (history.filterMap (fun event => (CausalJournal.old? event).bind Journal.encryption?)).length).map
      (CausalJournal.Event.old ∘ Journal.Event.encrypted)) =
    runPrefix (captureRun (liftWG (getTxSkb id))) w history
  simp only [runPrefix_captureRun]
  cases (liftWG (getTxSkb id)).run w <;>
    simp only [List.drop_length,List.map_nil,List.append_nil]

private theorem read_world (id : SkbId)
    (native : (liftWG (getTxSkb id)).run w = .ok (packet,v)) : v.wg = w.wg := by
  have keeps : Preserves (fun u : WGWorld => u = w.wg) (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u a value next b before run
    exact (Packets.getTxSkb_current id u next value a b run).1.trans before
  exact (hoare_iff_run _ _ _).mp (PublicationPoll.native_product _ _ keeps) w packet v rfl native

theorem branch_run (site : Decision) (value : Bool) (w : World) (history : List CausalJournal.Event) :
    runPrefix (ops.step (branch site value)) w history =
      (.ok (value,{w with ambient := CounterWindow.record w.ambient site value}),history) := by
  rw [step_eq]
  rfl

theorem guard_total (state : PacketState) (w : World) (history : List CausalJournal.Event) :
    ∃ v, runPrefix (guard state) w history = (.ok ((),v),history) ∧ v.wg = w.wg := by
  unfold guard
  split
  · simp only [runPrefix_bind,branch_run,runPrefix_pure]
    exact ⟨_,rfl,rfl⟩
  · exact ⟨w,rfl,rfl⟩

theorem head_current (performed : runPrefix (ops.head id) w history = (.ok (head,v),after)) :
    head.before = w ∧ head.after = v ∧ head.Valid (liftWG (getTxSkb id)) ∧
      v.wg = w.wg ∧ after = history := by
  rw [head_eq,runPrefix_captureRun] at performed
  cases native : (liftWG (getTxSkb id)).run w with
  | error reason => simp only [native] at performed; cases performed
  | ok out =>
    obtain ⟨packet,u⟩ := out
    simp only [native] at performed
    cases performed
    exact ⟨rfl,rfl,native,read_world id native,rfl⟩

theorem focused_accounted (encode : E → CausalJournal.Event) (decode : CausalJournal.Event → Option E)
    (birthFree : ∀ event, birthPackets (encode event) = []) (terminalFree : ∀ event, Quiet (encode event))
    (body : PrefixM E α) (action : Leanux.M α) (erases : ErasesPrefix body action)
    (keeps : Preserves (fun v : World => Inv history ledger debts locals v.wg) action)
    (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (focusPrefix encode decode body) w history = (.ok (value,v),after)) :
    Accounted after ledger debts locals v.wg := by
  have native := (focusPrefix_erases encode decode erases w history).symm.trans (congrArg Prod.fst performed)
  have entry := (hoare_iff_run _ _ _).mp keeps w value v before.entry native
  have grown := congrArg Prod.snd performed
  change history ++ _ = after at grown
  rw [← grown]
  apply (Accounted.mk entry before.complete).append_quiet
  · intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact birthFree original
  · intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact terminalFree original

theorem packet_keeps (head : RunWitness DataPacket) (id : SkbId) :
    Preserves (fun v : World => Inv history ledger debts locals v.wg)
      (do encryptPacket Env.checksumHelp head.value.keypair (← liftWG (getTxSkb id))) := by
  apply preserves_bind
  · apply (hoare_iff_run _ _ _).mpr
    intro w packet v before native
    exact (read_world id native) ▸ before
  · intro packet
    exact Encrypt.packet _ _

theorem packet_accounted (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (ops.packet headId head id) w history = (.ok (value,v),after)) :
    Accounted after ledger debts locals v.wg :=
  focused_accounted _ _ (fun _ => rfl) (fun _ _ => rfl) _ _
    (WorkerEncryption.packet_erases headId head id) (packet_keeps head id) before performed

theorem bytes_accounted (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (ops.step (liftWG (setTxSkb id fun p => {p with bytes}))) w history =
      (.ok ((),v),after)) : Accounted after ledger debts locals v.wg := by
  rw [step_eq,runPrefix_lift] at performed
  have same : history = after := congrArg Prod.snd performed
  subst after
  exact ⟨(hoare_iff_run _ _ _).mp (PublicationPoll.native_product _ _ (Encrypt.bytes id bytes))
    w () v before.entry (congrArg Prod.fst performed),before.complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPacket
