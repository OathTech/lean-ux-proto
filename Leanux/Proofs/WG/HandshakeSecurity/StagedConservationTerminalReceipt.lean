import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTerminalProjection
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalTxObserved

/-! Each terminal receipt records an actual completed native packet free at
its branch-labelled call site. The branch label is source evidence supplied
by createWith/bodyWith; validity alone does not assert a global partition. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues AuthenticatedEffects

structure Receipt where
  reason : Reason
  skb : SkbId
  run : RunWitness Unit

def Receipt.Valid (r : Receipt) : Prop := r.run.Valid (liftWG (freeTxSkb r.skb))

def Receipt.stamp (r : Receipt) : PacketStamp := packetStamp r.run.before.wg r.skb

def observed (record : Receipt → E) (free : PrefixM E Unit)
    (reason : Reason) (skb : SkbId) : PrefixM E Unit :=
  receiptObserved free (fun run => record ⟨reason,skb,run⟩)

theorem observed_completed (record : Receipt → E) (free : PrefixM E Unit)
    (reason : Reason) (skb : SkbId) (w v : World) (h tail : List E)
    (run : runPrefix free w h = (.ok ((),v),tail)) :
    runPrefix (observed record free reason skb) w h =
      (.ok ((),v),tail ++ [record ⟨reason,skb,⟨(),w,v⟩⟩]) := by
  rw [observed,runPrefix_receiptObserved,run]

theorem observed_stopped (record : Receipt → E) (free : PrefixM E Unit)
    (reason : Reason) (skb : SkbId) (w : World) (h tail : List E) (stop : Stop)
    (run : runPrefix free w h = (.error stop,tail)) :
    runPrefix (observed record free reason skb) w h = (.error stop,tail) := by
  rw [observed,runPrefix_receiptObserved,run]

theorem completed_valid (free : PrefixM E Unit) (reason : Reason) (skb : SkbId)
    (erases : ErasesPrefix free (liftWG (freeTxSkb skb)))
    (w v : World) (h tail : List E) (run : runPrefix free w h = (.ok ((),v),tail)) :
    (⟨reason,skb,⟨(),w,v⟩⟩ : Receipt).Valid :=
  (erases w h).symm.trans (congrArg Prod.fst run)

theorem observed_erases (record : Receipt → E) (free : PrefixM E Unit)
    (reason : Reason) (skb : SkbId)
    (erases : ErasesPrefix free (liftWG (freeTxSkb skb))) :
    ErasesPrefix (observed record free reason skb) (liftWG (freeTxSkb skb)) := by
  intro w h
  rw [observed,runPrefix_receiptObserved]
  have same := erases w h
  cases run : runPrefix free w h with
  | mk result events =>
    rw [run] at same
    cases result with
    | error stop => exact same
    | ok out => rcases out with ⟨value,state⟩; exact same

theorem observed_projects (record : Receipt → E) (ρ : E → Option F)
    (quiet : ∀ r, ρ (record r) = none)
    (free : PrefixM E Unit) (target : PrefixM F Unit)
    (projects : ProjectsPrefix ρ id free target) (reason : Reason) (skb : SkbId) :
    ProjectsPrefix ρ id (observed record free reason skb) target :=
  receiptObserved_projects (fun _ => quiet _) projects

/-- Successful native free identifies the resident input packet and its exact
post-state. This uses no reachable-state or lifetime invariant. -/
theorem native_free (skb : SkbId) (w v : World)
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    ∃ d packet, w.wg.dev = some d ∧ d.txSkbs[skb]? = some packet ∧
      v = {w with wg := Packets.update w.wg (fun device =>
        {device with txSkbs := device.txSkbs.erase skb})} := by
  rw [Leanux.Proofs.Framing.liftWG_run] at run
  cases device : w.wg.dev with
  | none =>
    simp only [freeTxSkb,liftSkb_run,device] at run
    cases run
  | some d =>
    cases packet : d.txSkbs[skb]? with
    | none =>
      simp [freeTxSkb,liftSkb_run,SkbStore.freeTx,SkbStore.getTx,device,packet,
        invariant,AmbientM.invariant] at run
      cases run
    | some found =>
      rw [Packets.freeTxSkb_run w.wg w.ambient d skb found device packet] at run
      cases run
      exact ⟨d,found,rfl,packet,rfl⟩

theorem Receipt.Valid.effects (r : Receipt) (valid : r.Valid) :
    ∃ d packet, r.run.before.wg.dev = some d ∧ d.txSkbs[r.skb]? = some packet ∧
      r.run.after = {r.run.before with wg := Packets.update r.run.before.wg (fun device =>
        {device with txSkbs := device.txSkbs.erase r.skb})} := by
  have run := valid
  change (liftWG (freeTxSkb r.skb)).run r.run.before = .ok (r.run.value,r.run.after) at run
  have unit : r.run.value = () := rfl
  rw [unit] at run
  exact native_free r.skb r.run.before r.run.after run

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
