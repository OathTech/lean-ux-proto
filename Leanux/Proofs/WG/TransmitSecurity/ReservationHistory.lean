import Leanux.Proofs.WG.TransmitSecurity.ReservationReceipts
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHistory

/-! Positional reservation evidence for actual allocation arguments. A packet
must name a completed native reservation in the strict preceding journal and
satisfy the message limit before allocation; numeric slots alone are not keys. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

variable {id : SkbId}

def Reserved (h : List Journal.Event) (slot nonce : Nat) : Prop :=
  ∃ r : WGRunWitness Nat, Journal.Event.reserved slot r ∈ h ∧
    r.Valid (Nonce.reserveNative slot) ∧ r.value = nonce ∧
    ∃ token, ReservationReceipts.Token slot r token ∧ Journal.Event.nonce token ∈ h

def Packets (h : List Journal.Event) (packets : List DataPacket) : Prop :=
  ∀ p ∈ packets, p.nonce < REJECT_AFTER_MESSAGES ∧ Reserved h p.keypair p.nonce

def Checked (pre : List Journal.Event) : Journal.Event → Prop
  | .allocated packets r => r.Valid (packets.mapM newTxSkb) ∧ Packets pre packets
  | _ => True

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked pre event

def allocation? : Journal.Event → Option (List DataPacket × WGRunWitness (List SkbId))
  | .allocated packets r => some (packets,r)
  | _ => none

def Monotone (P : List Journal.Event → Prop) : Prop := ∀ h k, h ⊆ k → P h → P k

def Keep (P : List Journal.Event → Prop) (h : List Journal.Event) (_ : WGWorld) (_ : Ambient) : Prop :=
  Safe h ∧ P h

theorem Reserved.mono (claim : Reserved h slot nonce) (included : h ⊆ k) : Reserved k slot nonce := by
  obtain ⟨r,member,valid,value,token,same,recorded⟩ := claim
  exact ⟨r,included member,valid,value,token,same,included recorded⟩

theorem Packets.mono (claim : Packets h packets) (included : h ⊆ k) : Packets k packets :=
  fun p member => ⟨(claim p member).1,((claim p member).2).mono included⟩

theorem Safe.append (old : Safe h)
    (new : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) : Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix old new

theorem Safe.quiet (old : Safe h) (quiet : allocation? event = none) : Safe (h ++ [event]) := by
  apply old.append
  intro pre e post position
  have member : e ∈ [event] := by rw [position]; simp
  have same := List.mem_singleton.mp member
  subst e
  cases event <;> simp_all only [allocation?,Checked,reduceCtorEq]

theorem Safe.quiet_suffix (old : Safe h) (quiet : suffix.filterMap allocation? = []) : Safe (h ++ suffix) := by
  apply old.append
  intro pre event post position
  cases event <;> simp only [Checked]
  rename_i packets run
  have member : Journal.Event.allocated packets run ∈ suffix := by rw [position]; simp
  have found : (packets,run) ∈ suffix.filterMap allocation? := List.mem_filterMap.mpr ⟨_,member,rfl⟩
  rw [quiet] at found
  cases found

theorem empty : Safe [] := by intro pre event post position; cases pre <;> cases position

theorem quiet {g : WGPrefix Journal.Event α} (appends : StateAppends g)
    (quiet : StateHistoryFrame allocation? g) (mono : Monotone P) :
    StatePrefixPreserves (Keep P) Safe g := by
  intro w a h hi
  obtain ⟨suffix,equal⟩ := appends w a h
  have excluded : suffix.filterMap allocation? = [] := by
    have same := quiet w a h
    rw [equal,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap allocation? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix (g.run w) a h).2 := by rw [equal]; exact hi.1.quiet_suffix excluded
  refine ⟨suffix,equal,safe,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    refine ⟨safe,?_⟩
    exact mono h _ (by intro e member; rw [equal]; exact List.mem_append_left _ member) hi.2

theorem lift (action : WG.M α) : StatePrefixPreserves (Keep P) Safe (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1) (fun _ _ _ _ _ _ hi _ => hi)

theorem pure (value : α) : StatePrefixPreserves (Keep P) Safe (Pure.pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.TransmitSecurity.ReservationHistory
