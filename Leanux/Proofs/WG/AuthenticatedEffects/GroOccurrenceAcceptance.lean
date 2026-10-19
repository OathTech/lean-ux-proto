import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceChecked
import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayHistory

/-! A GRO occurrence points back to its own candidate entry and immediately
following native replay receipt. Authentication is obtained from the same full
journal's initialized replay theorem, never from a different equal packet or
an unrelated earlier accepted receive. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
open Leanux Leanux.WG Leanux.Proofs.Logged

def Accepted (candidate : Nat → SkbId → RxPacket → E) (replay : TransportDriver.Replay → E)
    (entry : Entry) (history : List E) : Prop :=
  ∃ before receipt after,
    history = before ++ [candidate entry.scope entry.skb entry.packet, replay receipt] ++ after ∧
    entry.scope = before.length ∧ receipt.skb = entry.skb ∧ receipt.packet = entry.packet ∧
    receipt.run.value = true ∧ receipt.Valid

theorem accepted_monotone (candidate : Nat → SkbId → RxPacket → E)
    (replay : TransportDriver.Replay → E) : MonotoneWitness (Accepted candidate replay) := by
  intro entry history suffix accepted
  obtain ⟨before,receipt,after,position,index,skb,packet,value,valid⟩ := accepted
  refine ⟨before,receipt,after ++ suffix,?_,index,skb,packet,value,valid⟩
  simp only [position,List.append_assoc]

theorem Accepted.authenticated
    {candidate : Nat → SkbId → RxPacket → E} {record : TransportDriver.Replay → E}
    {entry : Entry} {history : List E} (accepted : Accepted candidate record entry history)
    (origin : E → Option TransportDriver.OriginEvent) (replay : E → Option TransportDriver.Replay)
    (inverse : ∀ receipt, replay (record receipt) = some receipt)
    (safe : TransportReplay.Safe origin replay history) :
    ∃ before receipt after,
      history = before ++ [candidate entry.scope entry.skb entry.packet,record receipt] ++ after ∧
      entry.scope = before.length ∧ receipt.skb = entry.skb ∧ receipt.packet = entry.packet ∧
      receipt.run.value = true ∧
      TransportReplay.Certified
        ((before ++ [candidate entry.scope entry.skb entry.packet]).filterMap origin) receipt := by
  obtain ⟨before,receipt,after,position,index,skb,packet,value,_⟩ := accepted
  refine ⟨before,receipt,after,position,index,skb,packet,value,?_⟩
  apply safe (before ++ [candidate entry.scope entry.skb entry.packet]) (record receipt) after
  · simpa only [List.append_assoc,List.cons_append,List.nil_append] using position
  · exact inverse receipt

def enter (candidate : Nat → SkbId → RxPacket → E) (skb : SkbId) (packet : RxPacket) : PrefixM E Nat :=
  fun w => ExceptT.mk fun h => (.ok (h.length,w),h ++ [candidate h.length skb packet])

def Entered (candidate : Nat → SkbId → RxPacket → E) (scope : Nat) (skb : SkbId)
    (packet : RxPacket) (history : List E) : Prop :=
  ∃ before, history = before ++ [candidate scope skb packet] ∧ scope = before.length

def Returned (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (scope : Nat) (skb : SkbId) (packet : RxPacket) (result : Bool) (history : List E) : Prop :=
  result = true → ∀ bytes, Accepted candidate record ⟨scope,skb,packet,bytes⟩ history

theorem enter_checked (candidate : Nat → SkbId → RxPacket → E)
    (record : TransportDriver.Replay → E) (Safe : List E → Prop)
    (quiet : ∀ history skb packet, Safe history → Safe (history ++ [candidate history.length skb packet]))
    (gro : Buffer) (skb : SkbId) (packet : RxPacket) :
    PrefixEnsures (fun h _ => Safe h ∧ gro.Ready (Accepted candidate record) h) Safe
      (enter candidate skb packet)
      (fun scope h _ => (Safe h ∧ gro.Ready (Accepted candidate record) h) ∧ Entered candidate scope skb packet h) := by
  intro w h input
  refine ⟨[candidate h.length skb packet],rfl,quiet h skb packet input.1,?_,?_⟩
  · exact ⟨quiet h skb packet input.1,input.2.append (accepted_monotone candidate record) _⟩
  · exact ⟨h,rfl,rfl⟩

theorem counter_checked (candidate : Nat → SkbId → RxPacket → E)
    (record : TransportDriver.Replay → E) (Safe : List E → Prop)
    (quiet : ∀ history receipt, Safe history → Safe (history ++ [record receipt]))
    (gro : Buffer) (scope : Nat) (skb : SkbId) (packet : RxPacket) :
    PrefixEnsures (fun h _ => (Safe h ∧ gro.Ready (Accepted candidate record) h) ∧
      Entered candidate scope skb packet h) Safe (TransportDriver.counter record skb packet)
      (fun result h _ => (Safe h ∧ gro.Ready (Accepted candidate record) h) ∧
        Returned candidate record scope skb packet result h) := by
  intro w h input
  rw [TransportDriver.counter_run]
  cases run : (liftWG (counterValidate packet.keypair packet.nonce)).run w with
  | error stop => exact ⟨[],by simp,input.1.1,True.intro⟩
  | ok output =>
    rcases output with ⟨result,v⟩
    let receipt : TransportDriver.Replay := ⟨skb,packet,⟨result,w,v⟩⟩
    refine ⟨[record receipt],rfl,quiet h receipt input.1.1,?_,?_⟩
    · exact ⟨quiet h receipt input.1.1,input.1.2.append (accepted_monotone candidate record) _⟩
    · intro success bytes
      obtain ⟨before,position,index⟩ := input.2
      refine ⟨before,receipt,[],?_,index,rfl,rfl,success,run⟩
      simp only [position,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,receipt]

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
