import Leanux.Proofs.WG.HandshakeSecurity.StagingMaterialInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialWorker
import Leanux.Proofs.WG.TransmitSecurity.ReservationBankEncryption

/-! One material-certified reservation bank per actual execution history.
The same bank supplies both positional exclusivity and key allocation binding;
independent existential assignments are never equated by their erased results. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity Responder ReservationAssignments
variable {u : Use} {packetIndex : Nat}

theorem Safe.at (safe : Safe h) (found : h[index]? = some (.allocated packets r)) :
    r.Valid (packets.mapM newTxSkb) ∧ Packets (h.take index) packets r.before := by
  obtain ⟨bound,value⟩ := List.getElem?_eq_some_iff.mp found
  apply safe (h.take index) (.allocated packets r) (h.drop (index + 1))
  rw [←value,List.getElem_cons_drop bound,List.take_append_drop]

noncomputable def bank (h : List Journal.Event) : Bank := by
  classical
  exact fun index => match h[index]? with
    | some (.allocated packets r) =>
        if claim : Packets (h.take index) packets r.before then claim.choose else []
    | _ => []

theorem bank_spec (safe : Safe h) (found : h[index]? = some (.allocated packets r)) :
    (bank h index).map Use.packet = packets ∧
    ((bank h index).map Use.position).Pairwise (· < ·) ∧
    ∀ u ∈ bank h index, u.Valid (h.take index) ∧ Available (h.take index) u.position ∧
      ∀ core, pool r.before u.packet.keypair = some core →
        pool u.reservation.before u.packet.keypair = some core := by
  have checked := (safe.at found).2
  simpa only [bank,found,checked,↓reduceDIte] using checked.choose_spec

theorem bank_valid (safe : Safe h) : BankValid h (bank h) := by
  intro index packets r found
  obtain ⟨mapped,ordered,entries⟩ := bank_spec safe found
  exact ⟨mapped,ordered,fun u member => ⟨(entries u member).1,(entries u member).2.1⟩⟩

theorem reservation_stamp (valid : ReservationReceipts.Token slot r token)
    (resident : pool r.before slot = some core) : token.stamp = core.allocation := by
  obtain ⟨_,d,k,device,key,rfl,_⟩ := valid
  have same : keyCore k = core := by simpa only [pool,device,Option.bind_some,key,Option.map_some,Option.some.injEq] using resident
  simpa only [keyCore,Nonce.allocation,Nonce.cell] using congrArg KeyCore.allocation same

/-- The actual allocation certificate chooses the same packet index in the
single material bank. Native AEAD residency then identifies its assigned
reservation allocation stamp, without assuming a surviving key credit. -/
theorem assigned_of_binding (safe : Safe h) (bound : ResidentMaterial.BoundReceipt h r) :
    ∃ token, Bank.Assigned (bank h) h r token ∧
      token.stamp = r.cipher.keyRead.value.internalId ∧ token.nonce = r.read.value.nonce := by
  obtain ⟨generation,epoch,packets,allocation,n,input,member,_,allocationEpoch,atInput,atId,material,resident⟩ := bound
  obtain ⟨before,after,position⟩ := List.mem_iff_append.mp member
  have found : h[before.length]? = some (.allocated packets allocation) := by
    rw [position]
    simp
  have mapped := (bank_spec safe found).1
  rw [←mapped,List.getElem?_map] at atInput
  cases atUse : (bank h before.length)[n]? with
  | none => simp [atUse] at atInput
  | some u =>
    rw [atUse] at atInput
    have same : u.packet = input := Option.some.inj atInput
    have assigned : Bank.Assigned (bank h) h r u.token :=
      ⟨before.length,packets,allocation,n,u,found,atUse,atId,
        allocationEpoch.trans epoch.symm,by rw [same]; exact material,rfl⟩
    refine ⟨u.token,assigned,?_,assigned.nonce (bank_valid safe)⟩
    have actual := (bank_spec safe found).2.2 u (List.mem_of_getElem? atUse)
    have atReservation := actual.2.2 (keyCore r.cipher.keyRead.value) (by simpa only [same] using resident)
    exact reservation_stamp actual.1.2.1 atReservation

/-- Initialization supplies the material bank and its positional validity;
there is no incoming reservation, reachability or key-continuity premise. -/
theorem initialized_bank (trace : Runner.Trace) (placeholders : Bool) :
    BankValid (runPrefixOuter (Journal.execute trace placeholders) []).2
      (bank (runPrefixOuter (Journal.execute trace placeholders) []).2) :=
  bank_valid (initialized trace placeholders)

/-- The material-certified bank retains the native exclusive-token result.
Identifying every final AEAD with its allocation certificate is a separate
resident-material state-transport obligation. -/
theorem initialized_exclusive (trace : Runner.Trace) (placeholders : Bool) :
    Bank.Exclusive (bank (runPrefixOuter (Journal.execute trace placeholders) []).2)
      (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  Bank.exclusive (initialized_bank trace placeholders)
    (Journal.initialized_reservations trace placeholders)
    (PacketOrigins.initialized trace placeholders) (EncryptionHistory.Scheduler.initialized trace placeholders)

/-- A resident allocation-entry key identifies the actual recorded reservation
receipt's core and allocation stamp in the same canonical bank. -/
theorem allocation_core (safe : Safe h) (found : h[index]? = some (.allocated packets r))
    (used : (bank h index)[packetIndex]? = some u)
    (resident : pool r.before u.packet.keypair = some core) :
    u.Valid h ∧ pool u.reservation.before u.packet.keypair = some core ∧
      u.token.stamp = core.allocation := by
  have valid := Bank.credit_valid (bank_valid safe) found used
  have material := (bank_spec safe found).2.2 u (List.mem_of_getElem? used) |>.2.2 core resident
  exact ⟨valid,material,reservation_stamp valid.2.1 material⟩

/-- Exact old-event projection transfers initialized material safety to the
final causal journal, including the events of a stopped execution. -/
theorem final_safe (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.old?) := by
  have history := congrArg Prod.snd (AuthenticatedEffects.CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [←history]
  exact initialized trace placeholders

theorem final_exclusive (trace : Runner.Trace) (placeholders : Bool) :
    let h := (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.old?
    Bank.Exclusive (bank h) h := by
  have history := congrArg Prod.snd (AuthenticatedEffects.CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  dsimp only
  rw [←history]
  exact initialized_exclusive trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
