import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootClaims

/-! Ordered causal tickets for actual handshake-work queue occurrences. A
journal position identifies the append; duplicate peer identifiers retain
separate tickets. Initialization and whole-driver transport stay explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged TimerRoot

structure Ticket where
  index : Nat
  receipt : Queued

def Ticket.peer (ticket : Ticket) : PeerId := ticket.receipt.peer

def Ticket.Valid (h : List Event) (ticket : Ticket) : Prop :=
  h[ticket.index]? = some (.queued ticket.receipt) ∧ ticket.receipt.Native

def queue (w : WGWorld) : List PeerId := (w.dev.map Device.sendWorkQueue).getD []

def Carrier (h : List Event) (tickets : List Ticket) (w : WGWorld) : Prop :=
  queue w = tickets.map Ticket.peer ∧ (tickets.map Ticket.index).Nodup ∧
    ∀ ticket ∈ tickets, ticket.Valid h

def Selected (tickets : List Ticket) (pid : PeerId) (ticket : Ticket) (rest : List Ticket) : Prop :=
  ∃ before after, tickets = before ++ ticket :: after ∧
    pid ∉ before.map Ticket.peer ∧ ticket.peer = pid ∧ rest = before ++ after

theorem Ticket.Valid.append {ticket : Ticket} {h : List Event} (valid : ticket.Valid h) (suffix : List Event) :
    ticket.Valid (h ++ suffix) := by
  refine ⟨?_,valid.2⟩
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp valid.1
  rw [List.getElem?_append_left bound]
  exact valid.1

theorem Ticket.Valid.position {ticket : Ticket} {h : List Event} (valid : ticket.Valid h) :
    ∃ before after, h = before ++ .queued ticket.receipt :: after ∧ before.length = ticket.index := by
  obtain ⟨bound,value⟩ := List.getElem?_eq_some_iff.mp valid.1
  refine ⟨h.take ticket.index,h.drop (ticket.index + 1),?_,?_⟩
  · rw [←value, List.getElem_cons_drop bound,List.take_append_drop]
  · simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt bound)]

theorem Carrier.append (carrier : Carrier h tickets w) (suffix : List Event) :
    Carrier (h ++ suffix) tickets w :=
  ⟨carrier.1,carrier.2.1,fun t member => (carrier.2.2 t member).append suffix⟩

theorem Carrier.frame (carrier : Carrier h tickets w) (same : queue v = queue w) : Carrier h tickets v :=
  ⟨same.trans carrier.1,carrier.2⟩

theorem Carrier.empty (w : WGWorld) (empty : queue w = []) : Carrier [] [] w :=
  ⟨empty,by simp,by simp⟩

theorem Carrier.enqueue (r : Queued) (carrier : Carrier h tickets r.run.before)
    (native : r.Native) (device : r.run.before.dev.isSome) :
    Carrier (h ++ [.queued r]) (tickets ++ [⟨h.length,r⟩]) r.run.after := by
  have queued := WorkRoot.queued_native_append r native
  have changeQueue : queue r.run.after = queue r.run.before ++ [r.peer] := by
    unfold queue
    rw [queued]
    cases hd : r.run.before.dev with
    | none => simp [hd] at device
    | some d => rfl
  refine ⟨?_,?_,?_⟩
  · simpa only [List.map_append,List.map_cons,List.map_nil,Ticket.peer] using changeQueue.trans
      (congrArg (fun qs => qs ++ [r.peer]) carrier.1)
  · simp only [List.map_append,List.map_cons,List.map_nil,List.nodup_append,List.nodup_cons,List.not_mem_nil,
      not_false_eq_true,List.nodup_nil,and_self]
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
    · exact (carrier.2.2 ticket old).append [.queued r]
    · simp only [List.mem_singleton] at fresh
      subst ticket
      exact ⟨by simp,native⟩

theorem select_exists (tickets : List Ticket) (pid : PeerId)
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

theorem Carrier.dequeue (carrier : Carrier h tickets w) (selected : Selected tickets pid ticket rest)
    (same : queue v = (queue w).erase pid) :
    ticket.Valid h ∧ Carrier h rest v := by
  have perm := selected.perm
  have valid : ∀ t ∈ ticket :: rest, t.Valid h :=
    fun t member => carrier.2.2 t (perm.mem_iff.mpr member)
  have unique := (perm.map Ticket.index).nodup carrier.2.1
  refine ⟨valid ticket (by simp),same.trans (by rw [carrier.1,selected.erase]),
    (List.nodup_cons.mp unique).2,?_⟩
  intro t member
  exact valid t (by simp [member])

theorem native_erase (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}).run w).run a =
      .ok (((),v),b)) : queue v = (queue w).erase pid := by
  cases run
  change ((w.dev.map (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})).map
    Device.sendWorkQueue).getD [] = _
  simp only [queue,Option.map_map,Function.comp_def]
  cases w.dev <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
