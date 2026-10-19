import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageSplit
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePollWitness

/-! A candidate scope is pending until its own native counter returns true.
Stops preserve pending prefixes; a rejected candidate may only leave its scope.
The real native branch, not the entry marker, discharges acceptance. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev CandidateToken (index : Nat) (skb : SkbId) (packet : RxPacket) : CausalScope.Token Cause :=
  ⟨index,.candidate skb packet⟩

def PendingFrames (frames : List (CausalScope.Token Cause)) (token : CausalScope.Token Cause)
    (history : List Event) : Prop :=
  Safe history ∧ CausalScope.stack (history.filterMap scope?) = .ok (token :: frames) ∧ Candidates frames history

def Pending (frames : List (CausalScope.Token Cause)) (index : Nat) (skb : SkbId)
    (packet : RxPacket) (history : List Event) : Prop :=
  PendingFrames frames (CandidateToken index skb packet) history ∧
    GroOccurrence.Entered candidate index skb packet history

def AtCounter (frames : List (CausalScope.Token Cause)) (index : Nat) (skb : SkbId)
    (packet : RxPacket) (result : Bool) (history : List Event) : Prop :=
  PendingFrames frames (CandidateToken index skb packet) history ∧
    (result = true → Accepted (CandidateToken index skb packet) history)

theorem PendingFrames.emit (ready : PendingFrames frames token history)
    (event : Event) (quiet : scope? event = none) (unprotected : ¬ Protected event) :
    PendingFrames frames token (history ++ [event]) := by
  refine ⟨ready.1.emit (fun relevant => (unprotected relevant).elim),?_,ready.2.2.append _⟩
  simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,List.append_nil] using ready.2.1

theorem PendingFrames.leave (ready : PendingFrames frames token history) :
    Inv frames (history ++ [.scope (.exited token.position)]) :=
  ⟨ready.1.emit (fun impossible => impossible.elim),
    CausalScope.stack_exited scope? Event.scope (fun _ => rfl) history frames token ready.2.1,
    ready.2.2.append _⟩

theorem AtCounter.accepted (ready : AtCounter frames index skb packet result history) (success : result = true) :
    Inv (CandidateToken index skb packet :: frames) history := by
  refine ⟨ready.1.1,ready.1.2.1,?_⟩
  intro token member
  rcases List.mem_cons.mp member with equal | earlier
  · subst token; exact ready.2 success
  · exact ready.1.2.2 token earlier

theorem candidate_enter (frames : List (CausalScope.Token Cause)) (skb : SkbId) (packet : RxPacket) :
    PrefixEnsures (fun h (_ : World) => Inv frames h) Safe
      (CausalSources.candidateEnter Event.scope skb packet)
      (fun index h (_ : World) => Pending frames index skb packet h) := by
  intro w h ready
  have safe := ready.1.emit (event := candidate h.length skb packet) (fun impossible => impossible.elim)
  refine ⟨[candidate h.length skb packet],rfl,safe,⟨safe,?_,ready.2.2.append _⟩,h,rfl,rfl⟩
  exact CausalScope.stack_entered scope? Event.scope (fun _ => rfl) h frames _ ready.2.1

theorem candidate_counter (frames : List (CausalScope.Token Cause)) (index : Nat)
    (skb : SkbId) (packet : RxPacket) :
    PrefixEnsures (fun h (_ : World) => Pending frames index skb packet h) Safe
      (TransportDriver.counter replay skb packet)
      (fun result h (_ : World) => AtCounter frames index skb packet result h) := by
  intro w h ready
  rw [TransportDriver.counter_run]
  cases run : (liftWG (counterValidate packet.keypair packet.nonce)).run w with
  | error stop => exact ⟨[],by simp,ready.1.1,True.intro⟩
  | ok output =>
    rcases output with ⟨result,v⟩
    let receipt : TransportDriver.Replay := ⟨skb,packet,⟨result,w,v⟩⟩
    have kept := ready.1.emit (replay receipt) rfl (fun impossible => impossible.elim)
    refine ⟨[replay receipt],rfl,kept.1,kept,?_⟩
    intro success
    obtain ⟨before,position,indexEq⟩ := ready.2
    refine ⟨before,receipt,[],?_,indexEq,rfl,rfl,success,run⟩
    simp only [position,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,receipt]

theorem candidate_enter_bind (skb : SkbId) (packet : RxPacket) (next : Nat → PrefixM Event α)
    (tail : ∀ index, PrefixEnsures (fun h (_ : World) => Pending frames index skb packet h) Safe (next index) Q) :
    PrefixEnsures (fun h (_ : World) => Inv frames h) Safe
      (CausalSources.candidateEnter Event.scope skb packet >>= next) Q :=
  PrefixEnsures.bind (candidate_enter frames skb packet) tail

theorem candidate_counter_bind (index : Nat) (skb : SkbId) (packet : RxPacket) (next : Bool → PrefixM Event α)
    (tail : ∀ result, PrefixEnsures (fun h (_ : World) => AtCounter frames index skb packet result h) Safe (next result) Q) :
    PrefixEnsures (fun h (_ : World) => Pending frames index skb packet h) Safe
      (TransportDriver.counter replay skb packet >>= next) Q :=
  PrefixEnsures.bind (candidate_counter frames index skb packet) tail

theorem candidate_leave_bind (index : Nat) (skb : SkbId) (packet : RxPacket) (result : Bool)
    (next : Unit → PrefixM Event α)
    (tail : ∀ value, PrefixEnsures (fun h (_ : World) => Inv frames h) Safe (next value) Q) :
    PrefixEnsures (fun h (_ : World) => AtCounter frames index skb packet result h) Safe
      (CausalScope.leavePrefix Event.scope index >>= next) Q := by
  apply PrefixEnsures.bind _ tail
  intro w h ready
  have popped := ready.1.leave
  exact ⟨[.scope (.exited index)],rfl,popped.1,popped⟩

theorem candidate_consume_bind (index : Nat) (skb : SkbId) (packet : RxPacket) (result : Bool)
    (success : result = true) (body : PrefixM Event α)
    (checked : ProductAt (CandidateToken index skb packet :: frames) body) (next : α → PrefixM Event β)
    (tail : ∀ value, PrefixEnsures (fun h (_ : World) => Inv (CandidateToken index skb packet :: frames) h)
      Safe (next value) Q) :
    PrefixEnsures (fun h (_ : World) => AtCounter frames index skb packet result h) Safe (body >>= next) Q :=
  PrefixEnsures.bind (checked.consequence (fun _ _ ready => ready.accepted success) (fun _ _ _ ready => ready)) tail

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
