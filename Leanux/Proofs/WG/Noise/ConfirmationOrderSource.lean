import Leanux.Proofs.WG.Noise.CounterConsumeClaims
import Leanux.Proofs.WG.Noise.ConfirmationOrderModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConfirmationOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes ConsumeConfirmation

def cut (r : RxDisposition.ConsumeReceipt) : Except Stop (WGRunWitness Bool) := do
  let (((), before), ambientBefore) ←
    ((setPeerEndpoint r.peer r.endpoint).run r.run.before).run r.run.ambientBefore
  let ((value, after), ambientAfter) ←
    ((receivedWithKeypair r.peer r.packet.keypair).run before).run ambientBefore
  return ⟨value,before,after,ambientBefore,ambientAfter⟩

def CutValid (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool) : Prop :=
  ((setPeerEndpoint r.peer r.endpoint).run r.run.before).run r.run.ambientBefore =
    .ok (((),c.before),c.ambientBefore) ∧
  c.Valid (receivedWithKeypair r.peer r.packet.keypair) ∧
  ((afterConfirmation r.peer r.packet c.value).run c.after).run c.ambientAfter =
    .ok ((r.run.value,r.run.after),r.run.ambientAfter)

theorem cut_eq (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool)
    (endpoint : ((setPeerEndpoint r.peer r.endpoint).run r.run.before).run r.run.ambientBefore =
      .ok (((),c.before),c.ambientBefore))
    (confirm : c.Valid (receivedWithKeypair r.peer r.packet.keypair)) :
    cut r = .ok c := by
  change ((receivedWithKeypair r.peer r.packet.keypair).run c.before).run c.ambientBefore =
    .ok ((c.value,c.after),c.ambientAfter) at confirm
  simp only [cut,endpoint,CounterWindow.except_ok_bind,confirm]
  rfl

theorem cut_valid (r : RxDisposition.ConsumeReceipt) (valid : r.Valid) :
    ∃ c, cut r = .ok c ∧ CutValid r c ∧ (projects r c).Valid ∧ (projects r c).Facts := by
  obtain ⟨c,endpoint,confirm,tail,facts⟩ := receipt_observation r valid
  exact ⟨c,cut_eq r c endpoint confirm,⟨endpoint,confirm,tail⟩,
    ⟨r,c,rfl,valid,endpoint,confirm,tail⟩,facts⟩

theorem cut_unique (r : RxDisposition.ConsumeReceipt) (a b : WGRunWitness Bool)
    (ha : CutValid r a) (hb : CutValid r b) : a = b :=
  Except.ok.inj ((cut_eq r a ha.1 ha.2.1).symm.trans (cut_eq r b hb.1 hb.2.1))

def packed (i n : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool) (allocation : Nat) : Record :=
  ⟨i,n,id,stamp,projects r c,allocation⟩

def fromReceipt (i n : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt) : Except Stop Record := do
  let c ← cut r
  match keyStampAt r.run.before r.packet.keypair with
  | none => .error (.invariant "confirmation receipt without a resident allocation stamp")
  | some allocation => .ok (packed i n id stamp r c allocation)

def Matches (i n : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt) (q : Record) : Prop :=
  r.Valid ∧ ∃ c allocation,
    CutValid r c ∧ keyStampAt r.run.before r.packet.keypair = some allocation ∧
    q = packed i n id stamp r c allocation

theorem fromReceipt_total (i n : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt) (valid : r.Valid)
    (resident : ∃ allocation, keyStampAt r.run.before r.packet.keypair = some allocation) :
    ∃ q, fromReceipt i n id stamp r = .ok q ∧ Matches i n id stamp r q := by
  obtain ⟨c,eq,source,cv,facts⟩ := cut_valid r valid
  obtain ⟨allocation,key⟩ := resident
  exact ⟨packed i n id stamp r c allocation,by simp only [fromReceipt,eq,CounterWindow.except_ok_bind,key],
    valid,c,allocation,source,key,rfl⟩

theorem matches_facts {i n : Nat} {id : SkbId} {stamp : PacketStamp}
    {r : RxDisposition.ConsumeReceipt} {q : Record} (matched : Matches i n id stamp r q) :
    q.position = i ∧ q.occurrence = n ∧ q.skb = id ∧ q.packetStamp = stamp ∧
    q.observation.Valid ∧ q.observation.Facts ∧
    projectedStampAt q.observation.entry q.observation.packet.keypair = some q.internalId ∧
    (q.observation.confirmed = true → q.observation.ConfirmedStamp q.internalId) := by
  obtain ⟨valid,c,allocation,source,key,rfl⟩ := matched
  have cv : (projects r c).Valid := ⟨r,c,rfl,valid,source⟩
  exact ⟨rfl,rfl,rfl,rfl,cv,observation_valid_facts _ cv,key,fun h => ⟨h,key⟩⟩

def Ready (e : RxHistory.Event) : Prop :=
  match e with
  | .consumed _ _ _ r =>
    r.Valid ∧ ∃ allocation, keyStampAt r.run.before r.packet.keypair = some allocation
  | _ => True

def fromEvent (i : Nat) (e : RxHistory.Event) : Except Stop (Option Record) :=
  match e with
  | .consumed n id stamp r => (fromReceipt i n id stamp r).map some
  | _ => .ok none

def EventMatches (i : Nat) (e : RxHistory.Event) (out : Option Record) : Prop :=
  match e with
  | .consumed n id stamp r => ∃ q, out = some q ∧ Matches i n id stamp r q
  | _ => out = none

theorem event_total (i : Nat) (e : RxHistory.Event) (ready : Ready e) :
    ∃ out, fromEvent i e = .ok out ∧ EventMatches i e out := by
  cases e with
  | consumed n id stamp r =>
    obtain ⟨q,eq,matched⟩ := fromReceipt_total i n id stamp r ready.1 ready.2
    exact ⟨some q,by simp only [fromEvent,eq,Except.map],q,rfl,matched⟩
  | _ => exact ⟨none,rfl,rfl⟩

theorem event_matches_position {i : Nat} {e : RxHistory.Event} {q : Record}
    (matched : EventMatches i e (some q)) : q.position = i := by
  cases e with
  | consumed n id stamp r =>
    obtain ⟨out,eq,matched⟩ := matched
    cases eq
    exact (matches_facts matched).1
  | _ => cases matched

def collectFrom (i : Nat) : List RxHistory.Event → Except Stop (List Record)
  | [] => .ok []
  | e :: es => do
    let q ← fromEvent i e
    let qs ← collectFrom (i+1) es
    return q.toList ++ qs

inductive Ordered : Nat → List RxHistory.Event → List Record → Prop where
  | nil (i : Nat) : Ordered i [] []
  | cons {i : Nat} {e : RxHistory.Event} {es : List RxHistory.Event}
      {q : Option Record} {qs : List Record}
      (head : EventMatches i e q) (tail : Ordered (i+1) es qs) :
      Ordered i (e::es) (q.toList ++ qs)

theorem collect_total (i : Nat) (es : List RxHistory.Event)
    (ready : ∀ e ∈ es, Ready e) :
    ∃ qs, collectFrom i es = .ok qs ∧ Ordered i es qs := by
  induction es generalizing i with
  | nil => exact ⟨[],rfl,.nil i⟩
  | cons e es ih =>
    obtain ⟨q,head,hm⟩ := event_total i e (ready e (by simp))
    obtain ⟨qs,tail,tm⟩ := ih (i+1) (fun x hx => ready x (List.mem_cons_of_mem _ hx))
    exact ⟨q.toList ++ qs,by simp only [collectFrom,head,CounterWindow.except_ok_bind,tail]; rfl,
      .cons hm tm⟩

theorem Ordered.eval {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) : collectFrom i es = .ok qs := by
  induction ordered with
  | nil => rfl
  | @cons i e es q qs matched tail ih =>
    have head : fromEvent i e = .ok q := by
      cases e with
      | consumed n id stamp r =>
        obtain ⟨out,rfl,valid,c,allocation,source,key,rfl⟩ := matched
        simp only [fromEvent,fromReceipt,cut_eq r c source.1 source.2.1,
          CounterWindow.except_ok_bind,key,Except.map]
      | _ => rw [matched]; rfl
    simp only [collectFrom,head,CounterWindow.except_ok_bind,ih]
    rfl

theorem Ordered.sound {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) (q : Record) (member : q ∈ qs) :
    ∃ pre e post, es = pre ++ e::post ∧
      EventMatches (i+pre.length) e (some q) := by
  induction ordered with
  | nil => cases member
  | @cons i e es out qs matched tail ih =>
    rcases List.mem_append.mp member with head | later
    · cases out with
      | none => cases head
      | some first =>
        have equal : q = first := by simpa using head
        subst q
        exact ⟨[],e,es,rfl,matched⟩
    · obtain ⟨pre,event,post,eq,hm⟩ := ih later
      refine ⟨e::pre,event,post,by simp only [eq,List.cons_append],?_⟩
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hm

theorem Ordered.complete {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) (pre post : List RxHistory.Event)
    (n id : Nat) (stamp : PacketStamp) (r : RxDisposition.ConsumeReceipt)
    (position : es = pre ++ .consumed n id stamp r :: post) :
    ∃ before q after, qs = before ++ q :: after ∧
      Matches (i+pre.length) n id stamp r q := by
  induction pre generalizing i es qs with
  | nil =>
    simp only [List.nil_append] at position
    subst es
    cases ordered with
    | @cons _ _ _ out qs matched tail =>
      obtain ⟨q,rfl,hm⟩ := matched
      exact ⟨[],q,qs,rfl,hm⟩
  | cons e pre ih =>
    simp only [List.cons_append] at position
    subst es
    cases ordered with
    | @cons _ _ _ out qs matched tail =>
      obtain ⟨before,q,after,eq,hm⟩ := ih tail rfl
      refine ⟨out.toList ++ before,q,after,?_,?_⟩
      · rw [eq,List.append_assoc]
      · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hm

theorem Ordered.lower {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) (q : Record) (member : q ∈ qs) : i ≤ q.position := by
  obtain ⟨pre,e,post,eq,matched⟩ := ordered.sound q member
  rw [event_matches_position matched]
  exact Nat.le_add_right _ _

theorem Ordered.increasing {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) :
    qs.Pairwise (fun a b => a.position < b.position) := by
  induction ordered with
  | nil => exact List.Pairwise.nil
  | @cons i e es out qs matched tail ih =>
    cases out with
    | none => exact ih
    | some q =>
      apply List.Pairwise.cons _ ih
      intro later member
      rw [event_matches_position matched]
      exact Nat.lt_of_succ_le (tail.lower later member)

def consumedCount : List RxHistory.Event → Nat
  | [] => 0
  | .consumed _ _ _ _ :: es => consumedCount es + 1
  | _ :: es => consumedCount es

theorem Ordered.length {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) : qs.length = consumedCount es := by
  induction ordered with
  | nil => rfl
  | @cons i e es out qs matched tail ih =>
    cases e with
    | consumed n id stamp r =>
      obtain ⟨q,rfl,matched⟩ := matched
      simpa only [Option.toList_some,List.singleton_append,List.length_cons,
        consumedCount,Nat.add_comm 1] using congrArg (·+1) ih
    | _ => rw [matched]; exact ih

theorem successful_append (a b : List Record) :
    successful (a++b) = successful a ++ successful b := List.filterMap_append

theorem Ordered.success_sound {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) (allocation : Nat) (member : allocation ∈ successful qs) :
    ∃ (pre post : List RxHistory.Event) (n id : Nat) (stamp : PacketStamp)
      (r : RxDisposition.ConsumeReceipt) (q : Record),
      es = pre ++ .consumed n id stamp r :: post ∧ q ∈ qs ∧
      Matches (i+pre.length) n id stamp r q ∧
      q.observation.confirmed = true ∧ q.internalId = allocation := by
  obtain ⟨q,member,selected⟩ := List.mem_filterMap.mp member
  have selected' : q.observation.confirmed = true ∧ q.internalId = allocation := by
    split at selected <;> simp_all
  obtain ⟨pre,e,post,position,matched⟩ := ordered.sound q member
  cases e with
  | consumed n id stamp r =>
    obtain ⟨out,eq,hm⟩ := matched
    cases eq
    exact ⟨pre,post,n,id,stamp,r,q,position,member,hm,selected'⟩
  | _ => cases matched

theorem Ordered.success_complete {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) (pre post : List RxHistory.Event)
    (n id : Nat) (stamp : PacketStamp) (r : RxDisposition.ConsumeReceipt)
    (position : es = pre ++ .consumed n id stamp r :: post)
    (c : WGRunWitness Bool) (cutSource : CutValid r c) (confirmed : c.value = true) :
    ∃ left allocation right, successful qs = left ++ allocation :: right ∧
      keyStampAt r.run.before r.packet.keypair = some allocation := by
  obtain ⟨before,q,after,eq,valid,actual,allocation,source,key,rfl⟩ :=
    ordered.complete pre post n id stamp r position
  have same := cut_unique r actual c source cutSource
  subst actual
  refine ⟨successful before,allocation,successful after,?_,key⟩
  rw [eq,successful_append]
  simp only [successful,List.filterMap_cons,packed,projects,confirmed,ite_true,
    List.filterMap_cons]

def history (trace : Runner.Trace) (placeholders : Bool) : List RxHistory.Event :=
  (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2

theorem initialized_ready (trace : Runner.Trace) (placeholders : Bool)
    (e : RxHistory.Event) (member : e ∈ history trace placeholders) : Ready e := by
  cases e with
  | consumed n id stamp r =>
    obtain ⟨pre,post,position⟩ := List.append_of_mem member
    have pos : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
        pre ++ .consumed n id stamp r :: post := position
    obtain ⟨a,b,decrypt,out,pid,published,ambient,journal,publication,certified⟩ :=
      PublicationRunner.consumed trace placeholders pre post n id stamp r pos
    exact ⟨certified.1.1,
      CounterConsume.initialized_consumed_stamp trace placeholders pre post n id stamp r pos⟩
  | _ => trivial

def observations (trace : Runner.Trace) (placeholders : Bool) : Except Stop (List Record) :=
  collectFrom 0 (history trace placeholders)

def confirmationIds (trace : Runner.Trace) (placeholders : Bool) : Except Stop (List Nat) :=
  (observations trace placeholders).map successful

theorem initialized_ordered (trace : Runner.Trace) (placeholders : Bool) :
    ∃ qs, observations trace placeholders = .ok qs ∧
      confirmationIds trace placeholders = .ok (successful qs) ∧
      Ordered 0 (history trace placeholders) qs := by
  obtain ⟨qs,eq,ordered⟩ := collect_total 0 (history trace placeholders)
    (initialized_ready trace placeholders)
  exact ⟨qs,eq,by simp only [confirmationIds,observations,eq,Except.map],ordered⟩

def OccursAt (trace : Runner.Trace) (placeholders : Bool) (q : Record) : Prop :=
  ∃ (pre post : List RxHistory.Event) (r : RxDisposition.ConsumeReceipt),
    history trace placeholders = pre ++ .consumed q.occurrence q.skb q.packetStamp r :: post ∧
    q.position = pre.length ∧ Matches q.position q.occurrence q.skb q.packetStamp r q

theorem Ordered.occurs {trace : Runner.Trace} {placeholders : Bool} {qs : List Record}
    (ordered : Ordered 0 (history trace placeholders) qs) (q : Record) (member : q ∈ qs) :
    OccursAt trace placeholders q := by
  obtain ⟨pre,e,post,position,matched⟩ := ordered.sound q member
  cases e with
  | consumed n id stamp r =>
    obtain ⟨out,eq,hm⟩ := matched
    cases eq
    obtain ⟨pi,pn,pk,ps,_⟩ := matches_facts hm
    simp only [Nat.zero_add] at pi hm
    refine ⟨pre,post,r,?_,pi,?_⟩
    · simpa only [pn,pk,ps] using position
    · simpa only [pi,pn,pk,ps] using hm
  | _ => cases matched

theorem occurs_facts {trace : Runner.Trace} {placeholders : Bool} {q : Record}
    (occurs : OccursAt trace placeholders q) :
    CounterConsume.Occurs trace placeholders q.occurrence q.skb q.packetStamp q.observation ∧
    q.observation.Valid ∧ q.observation.Facts ∧
    projectedStampAt q.observation.entry q.observation.packet.keypair = some q.internalId ∧
    (q.observation.confirmed = true → q.observation.ConfirmedStamp q.internalId) := by
  obtain ⟨pre,post,r,position,index,matched⟩ := occurs
  have facts := matches_facts matched
  obtain ⟨valid,c,allocation,source,key,eq⟩ := matched
  refine ⟨?_,facts.2.2.2.2⟩
  refine ⟨pre,post,r,c,position,?_,valid,source⟩
  exact congrArg Record.observation eq.symm

theorem matches_unique {i n : Nat} {id : SkbId} {stamp : PacketStamp}
    {r : RxDisposition.ConsumeReceipt} {a b : Record}
    (ha : Matches i n id stamp r a) (hb : Matches i n id stamp r b) : a = b := by
  obtain ⟨va,ca,sa,sourceA,keyA,rfl⟩ := ha
  obtain ⟨vb,cb,sb,sourceB,keyB,rfl⟩ := hb
  have sourceEq := cut_unique r ca cb sourceA sourceB
  have stampEq := Option.some.inj (keyA.symm.trans keyB)
  cases sourceEq
  cases stampEq
  rfl

theorem Ordered.complete_occurs {trace : Runner.Trace} {placeholders : Bool} {qs : List Record}
    (ordered : Ordered 0 (history trace placeholders) qs) (q : Record)
    (occurs : OccursAt trace placeholders q) : q ∈ qs := by
  obtain ⟨pre,post,r,position,index,matched⟩ := occurs
  obtain ⟨before,found,after,eq,hm⟩ :=
    ordered.complete pre post q.occurrence q.skb q.packetStamp r position
  have hm' : Matches q.position q.occurrence q.skb q.packetStamp r found := by
    simpa only [Nat.zero_add,index] using hm
  have equal := matches_unique matched hm'
  subst found
  rw [eq]
  exact List.mem_append_cons_self

theorem initialized_event (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (n id : Nat) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : history trace placeholders = pre ++ .consumed n id stamp r :: post) :
    ∃ q, OccursAt trace placeholders q ∧ q.position = pre.length ∧
      q.occurrence = n ∧ q.skb = id ∧ q.packetStamp = stamp ∧
      Matches pre.length n id stamp r q := by
  obtain ⟨qs,eq,ids,ordered⟩ := initialized_ordered trace placeholders
  obtain ⟨before,q,after,split,matched⟩ := ordered.complete pre post n id stamp r position
  have member : q ∈ qs := by rw [split]; exact List.mem_append_cons_self
  have facts := matches_facts matched
  exact ⟨q,ordered.occurs q member,by simpa only [Nat.zero_add] using facts.1,
    facts.2.1,facts.2.2.1,facts.2.2.2.1,by simpa only [Nat.zero_add] using matched⟩

end Leanux.Proofs.WG.Noise.ConfirmationOrder
