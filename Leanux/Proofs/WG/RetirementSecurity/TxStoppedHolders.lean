import Leanux.Proofs.WG.RetirementSecurity.TxPeekHolders
import Leanux.Proofs.WG.RetirementSecurity.TxDisposeHolders

/-! An original TX worker iteration returning false has only peeked its
queue. The source cannot enter disposal and then report a stopped iteration:
normal disposal returns true. Thus empty and uncrypted stops retain all key
holders without assumptions about later completion. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def txReadySource (first : Option (List SkbId)) : WG.M Bool :=
  WG.andM (branch .txPacket first.isSome) do
    let some item := first | invariant "unreachable"
    let some head := item.head? | invariant "an empty ring item"
    branch .txNotUncrypted ((← getTxSkb head).state != .uncrypted)

def txBeforeDispose (pid : PeerId) (items : List SkbId) (head : DataPacket) : WG.M Unit := do
  setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}
  if ← branch .txCrypted (head.state == .crypted) then createDataDone pid items

def txReadyTail (pid : PeerId) (first : Option (List SkbId)) : WG.M Bool := do
  let some items := first | invariant "unreachable"
  let some headId := items.head? | invariant "an empty ring item"
  let head ← getTxSkb headId
  txBeforeDispose pid items head
  Queues.TxDisposition.disposeSource pid items head.keypair

theorem tx_body_factor (pid : PeerId) (first : Option (List SkbId)) :
    Queues.TxDisposition.bodySource pid first = (do
      let ready ← txReadySource first
      if !ready then return false
      txReadyTail pid first) := by
  simp only [Queues.TxDisposition.bodySource,txReadySource,txReadyTail,txBeforeDispose,
    bind_assoc,Queues.RxCredits.bind_if_source,pure_bind]
  rfl

theorem ready_world_frame (first : Option (List SkbId)) (P : WGWorld → Prop) :
    Preserves P (txReadySource first) := by
  have read (head : SkbId) : Preserves P (getTxSkb head) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a packet v b before run
    exact (Packets.getTxSkb_current head w v packet a b run).1 ▸ before
  have ambient {α : Type} (action : AmbientM α) :
      Preserves P (monadLift action : WG.M α) := hoare_liftAmbient action P
  unfold txReadySource WG.andM
  simp only [branch,invariant]
  repeat' first
    | (allocation_release_head getTxSkb; exact read _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem ready_tail_true (pid : PeerId) (first : Option (List SkbId)) :
    Hoare (txReadyTail pid first) (fun _ => True) (fun result _ => result = true) := by
  have ignore {α : Type} (action : WG.M α) : Hoare action (fun _ => True) (fun _ _ => True) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro _ _ _ _ _ _ _
    trivial
  unfold txReadyTail
  cases first with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro _ _ _ _ _ _ run
    cases run
  | some items =>
    cases head : items.head? with
    | none =>
      simp only [head]
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro _ _ _ _ _ _ run
      cases run
    | some headId =>
      simp only [head]
      apply hoare_bind _ _ (ignore (getTxSkb headId))
      intro packet
      apply hoare_bind _ _ (ignore (txBeforeDispose pid items packet))
      intro _
      exact hoare_consequence (Queues.TxDisposition.dispose_packets pid items packet.keypair)
        (fun _ h => h) (fun _ _ h => h.1)

theorem body_false_world (pid : PeerId) (first : Option (List SkbId)) (a b : Ambient)
    (run : ((Queues.TxDisposition.bodySource pid first).run w).run a = .ok ((false,v),b)) : v = w := by
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,testRun,tail⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp (ready_world_frame first (fun s => s = w))
    w a ready u c rfl testRun
  cases ready with
  | false => simp only [Bool.not_false,ite_true] at tail; cases tail; exact same
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    have impossible := (hoare_iff_run_ambient _ _ _).mp (ready_tail_true pid first)
      u c false v b True.intro tail
    contradiction

theorem HolderAccount.tx_stopped (account : HolderAccount temporary w)
    (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((false,v),b)) : HolderAccount temporary v := by
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,peek,body⟩ := run
  have same := body_false_world pid first c b body
  rw [same]
  exact (account.peek_tx pid a c peek).1

end Leanux.Proofs.WG.RetirementSecurity
