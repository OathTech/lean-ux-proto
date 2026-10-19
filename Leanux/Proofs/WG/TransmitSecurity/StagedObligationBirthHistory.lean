import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionLedger

/-! The obligation domain is read from the actual final journal. It includes
every successful routing batch and generated keepalive occurrence, with exact
source positions and ordinals. Choosing a smaller existential birth list cannot
satisfy this domain. Native validity of each receipt is a separate source fact. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects CausalJournal

/-- The packet list affects only the birth count here; no packet bytes are
used to identify or deduplicate an occurrence. -/
def birthPackets : Event → List Packet
  | .old (.routed _ _ packets mtu run) =>
    match run.value with
    | .ok _ => packets.map (fun packet => {packet with mtu})
    | .error _ => []
  | .keepalivePrepared pid run =>
    if run.value then
      match stagedAt run.before pid with
      | some (_,[]) => [{}]
      | _ => []
    else []
  | _ => []

def birthsFrom (start : Nat) : List Event → List Ticket
  | [] => []
  | event :: rest => freshTickets start 0 (birthPackets event) ++ birthsFrom (start+1) rest

def births (history : List Event) : List Ticket := birthsFrom 0 history

theorem birthsFrom_append (left right : List Event) (start : Nat) :
    birthsFrom start (left ++ right) = birthsFrom start left ++ birthsFrom (start+left.length) right := by
  induction left generalizing start with
  | nil => simp [birthsFrom]
  | cons event rest ih =>
    simp only [List.cons_append,birthsFrom,ih,List.length_cons,List.append_assoc]
    simp only [Nat.add_comm,Nat.add_left_comm]

theorem births_emit (history : List Event) (event : Event) :
    births (history ++ [event]) = births history ++ freshTickets history.length 0 (birthPackets event) := by
  simp only [births,birthsFrom_append,birthsFrom,List.append_nil,Nat.zero_add]

theorem birthsFrom_bounds (member : ticket ∈ birthsFrom start history) :
    start ≤ ticket.position ∧ ticket.position < start + history.length := by
  induction history generalizing start with
  | nil => cases member
  | cons event rest ih =>
    rcases List.mem_append.mp member with fresh | later
    · have same := (freshTickets_fields fresh).1
      simp only [List.length_cons]
      omega
    · have bounded := ih later
      simp only [List.length_cons]
      omega

theorem birthsFrom_unique (start : Nat) (history : List Event) : (birthsFrom start history).Nodup := by
  induction history generalizing start with
  | nil => exact .nil
  | cons event rest ih =>
    apply List.nodup_append.mpr
    refine ⟨freshTickets_unique _ _ _,ih (start+1),?_⟩
    intro first inFirst second inSecond equal
    have atStart := (freshTickets_fields inFirst).1
    have afterStart := (birthsFrom_bounds inSecond).1
    subst second
    omega

theorem births_bounded (history : List Event) : StagedAdmission.Bounded history.length (births history) := by
  intro ticket member
  have bound := (birthsFrom_bounds member).2
  simpa using bound

theorem births_unique (history : List Event) : (births history).Nodup := birthsFrom_unique 0 history

/-- An event with no admission cannot change the fixed obligation domain. -/
theorem births_quiet (history : List Event) (quiet : birthPackets event = []) :
    births (history ++ [event]) = births history := by
  rw [births_emit,quiet]
  simp only [freshTickets,List.append_nil]

theorem birthsFrom_quiet (start : Nat) (history : List Event)
    (quiet : ∀ event ∈ history, birthPackets event = []) : birthsFrom start history = [] := by
  induction history generalizing start with
  | nil => rfl
  | cons event rest ih =>
    simp only [birthsFrom,quiet event (List.mem_cons_self ..),freshTickets,List.nil_append]
    exact ih (start+1) (fun entry member => quiet entry (List.mem_cons_of_mem _ member))

theorem births_quiet_suffix (history suffix : List Event)
    (quiet : ∀ event ∈ suffix, birthPackets event = []) :
    births (history ++ suffix) = births history := by
  rw [births,birthsFrom_append,birthsFrom_quiet _ _ quiet,List.append_nil]
  rfl

/-- Extending the journal with an actual admission produces exactly its fresh
tickets. Strict position bounds and distinctness require no incoming premise. -/
theorem admit_canonical (valid : Valid (births history) ledger)
    (location : Pending) (event : Event) :
    Valid (births (history ++ [event]))
      (StagedAdmission.appendBirths ledger history.length location (birthPackets event)) := by
  rw [births_emit]
  exact StagedAdmission.valid valid (births_bounded history)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
