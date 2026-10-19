import Leanux.Proofs.WG.AuthenticatedEffects.CausalSourceMetadata
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsReceipts

/-! One causal ticket per actual send-work append in the full joint journal.
Repeated peer identifiers retain separate positions. Native queue selection
must provide membership before the first matching ticket can be consumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.QueuedOccurrences
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Ticket (Cause : Type) where
  index : Nat
  receipt : TimerEffects.Queued Cause

def Ticket.peer (ticket : Ticket Cause) : PeerId := ticket.receipt.peer

def Ticket.Valid (record : TimerEffects.Queued Cause → E) (h : List E) (ticket : Ticket Cause) : Prop :=
  h[ticket.index]? = some (record ticket.receipt) ∧ ticket.receipt.Valid

def queue (w : WGWorld) : List PeerId := (w.dev.map Device.sendWorkQueue).getD []

def Carrier (record : TimerEffects.Queued Cause → E) (h : List E) (tickets : List (Ticket Cause))
    (w : WGWorld) : Prop :=
  queue w = tickets.map Ticket.peer ∧ (tickets.map Ticket.index).Nodup ∧
    ∀ ticket ∈ tickets, ticket.Valid record h

def Selected (tickets : List (Ticket Cause)) (pid : PeerId) (ticket : Ticket Cause)
    (rest : List (Ticket Cause)) : Prop :=
  ∃ before after, tickets = before ++ ticket :: after ∧
    pid ∉ before.map Ticket.peer ∧ ticket.peer = pid ∧ rest = before ++ after

variable {record : TimerEffects.Queued Cause → E}
  {h : List E} {tickets rest : List (Ticket Cause)} {ticket : Ticket Cause}
  {w v : WGWorld} {pid : PeerId}

theorem Ticket.Valid.append (valid : ticket.Valid record h) (suffix : List E) :
    ticket.Valid record (h ++ suffix) := by
  refine ⟨?_,valid.2⟩
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp valid.1
  rw [List.getElem?_append_left bound]
  exact valid.1

theorem Ticket.Valid.position (valid : ticket.Valid record h) :
    ∃ before after, h = before ++ record ticket.receipt :: after ∧ before.length = ticket.index := by
  obtain ⟨bound,value⟩ := List.getElem?_eq_some_iff.mp valid.1
  refine ⟨h.take ticket.index,h.drop (ticket.index + 1),?_,?_⟩
  · rw [←value,List.getElem_cons_drop bound,List.take_append_drop]
  · simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt bound)]

theorem Carrier.append (carrier : Carrier record h tickets w) (suffix : List E) :
    Carrier record (h ++ suffix) tickets w :=
  ⟨carrier.1,carrier.2.1,fun t member => (carrier.2.2 t member).append suffix⟩

theorem Carrier.frame (carrier : Carrier record h tickets w) (same : queue v = queue w) :
    Carrier record h tickets v := ⟨same.trans carrier.1,carrier.2⟩

theorem Carrier.empty (w : WGWorld) (empty : queue w = []) : Carrier record [] [] w :=
  ⟨empty,by simp,by simp⟩

theorem native_append (r : TimerEffects.Queued Cause) (native : r.Valid) :
    r.run.after.dev = r.run.before.dev.map
      (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [r.peer]}) := by
  rcases r with ⟨cause,pid,⟨value,w,v,a,b⟩⟩
  change ((modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}).run w).run a =
    .ok ((value,v),b) at native
  have states := congrArg (fun z => z.toOption.map (fun x => x.1.2.dev)) native
  exact (Option.some.inj states).symm

theorem Carrier.enqueue (r : TimerEffects.Queued Cause)
    (carrier : Carrier record h tickets r.run.before) (native : r.Valid)
    (device : r.run.before.dev.isSome) :
    Carrier record (h ++ [record r]) (tickets ++ [⟨h.length,r⟩]) r.run.after := by
  have changeQueue : queue r.run.after = queue r.run.before ++ [r.peer] := by
    unfold queue
    rw [native_append r native]
    cases hd : r.run.before.dev with
    | none => simp [hd] at device
    | some d => rfl
  refine ⟨?_,?_,?_⟩
  · simpa only [List.map_append,List.map_cons,List.map_nil,Ticket.peer] using changeQueue.trans
      (congrArg (fun qs => qs ++ [r.peer]) carrier.1)
  · simp only [List.map_append,List.map_cons,List.map_nil,List.nodup_append,List.nodup_cons,
      List.not_mem_nil,not_false_eq_true,List.nodup_nil,and_self]
    refine ⟨carrier.2.1,?_,?_⟩
    · trivial
    · intro index member other singleton
      simp only [List.mem_singleton] at singleton
      subst other
      obtain ⟨ticket,inside,rfl⟩ := List.mem_map.mp member
      have bound := (List.getElem?_eq_some_iff.mp (carrier.2.2 ticket inside).1).1
      omega
  · intro ticket member
    rcases List.mem_append.mp member with old | fresh
    · exact (carrier.2.2 ticket old).append [record r]
    · simp only [List.mem_singleton] at fresh
      subst ticket
      exact ⟨by simp,native⟩

theorem select_exists (tickets : List (Ticket Cause)) (pid : PeerId)
    (present : pid ∈ tickets.map Ticket.peer) : ∃ ticket rest, Selected tickets pid ticket rest := by
  induction tickets with
  | nil => simp at present
  | cons head tail ih =>
    by_cases same : head.peer = pid
    · exact ⟨head,tail,[],tail,rfl,by simp,same,rfl⟩
    · have inside : pid ∈ tail.map Ticket.peer := by simpa [same,Ne.symm same] using present
      obtain ⟨ticket,rest,before,after,split,absent,peer,restEq⟩ := ih inside
      refine ⟨ticket,head :: rest,head :: before,after,?_,?_,peer,?_⟩
      · simp [split]
      · simp [Ne.symm same,absent]
      · simp [restEq]

theorem Selected.perm (selected : Selected tickets pid ticket rest) : tickets.Perm (ticket :: rest) := by
  obtain ⟨before,after,rfl,_,_,rfl⟩ := selected
  exact List.perm_middle

theorem Selected.erase (selected : Selected tickets pid ticket rest) :
    (tickets.map Ticket.peer).erase pid = rest.map Ticket.peer := by
  obtain ⟨before,after,rfl,absent,peer,rfl⟩ := selected
  simp only [List.map_append,List.map_cons,peer]
  rw [List.erase_append_right _ absent,List.erase_cons_head]

theorem Carrier.dequeue (carrier : Carrier record h tickets w) (selected : Selected tickets pid ticket rest)
    (same : queue v = (queue w).erase pid) :
    ticket.Valid record h ∧ Carrier record h rest v := by
  have perm := selected.perm
  have valid : ∀ t ∈ ticket :: rest, t.Valid record h :=
    fun t member => carrier.2.2 t (perm.mem_iff.mpr member)
  have unique := (perm.map Ticket.index).nodup carrier.2.1
  refine ⟨valid ticket (by simp),same.trans (by rw [carrier.1,selected.erase]),
    (List.nodup_cons.mp unique).2,?_⟩
  intro t member
  exact valid t (by simp [member])

/-- The occurrence exists only under the native caller's membership fact.
It keeps its own causal receipt and exact journal position despite duplicates. -/
theorem Carrier.selected (carrier : Carrier record h tickets w) (present : pid ∈ queue w) :
    ∃ ticket rest before after, Selected tickets pid ticket rest ∧ ticket.peer = pid ∧
      h = before ++ record ticket.receipt :: after ∧ before.length = ticket.index ∧ ticket.receipt.Valid := by
  obtain ⟨ticket,rest,selected⟩ := select_exists tickets pid (carrier.1 ▸ present)
  have decomposition := selected
  obtain ⟨left,right,split,_,same,_⟩ := decomposition
  have valid := carrier.2.2 ticket (by rw [split]; simp)
  obtain ⟨before,after,position,index⟩ := valid.position
  exact ⟨ticket,rest,before,after,selected,same,position,index,valid.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.QueuedOccurrences
