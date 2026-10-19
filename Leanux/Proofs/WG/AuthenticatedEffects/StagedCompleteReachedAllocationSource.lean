import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldAllocationSource

/-! Actual source intervals of the ordered native batch allocator. The
constructors follow only its fixed newTxSkb calls, rather than arbitrary
extensionally equal factors. Intermediate cells precede the batch receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations

/-- A native prefix after exactly n calls in this concrete mapM loop. The
ambient value is unchanged by each real allocation primitive. -/
inductive Path : List DataPacket→WGWorld→Ambient→Nat→List SkbId→WGWorld→Prop where
  | zero : Path packets w a 0 [] w
  | step {skb : SkbId} (first : ((newTxSkb packet).run w).run a=.ok ((skb,u),a))
      (tail : Path packets u a n items v) :
      Path (packet::packets) w a (n+1) (skb::items) v

theorem Path.bound (path : Path packets w a n items v) : n≤packets.length := by
  induction path with
  | zero=>exact Nat.zero_le _
  | step _ _ ih=>simpa only [List.length_cons] using Nat.succ_le_succ ih

theorem Path.length (path : Path packets w a n items v) : items.length=n := by
  induction path with
  | zero=>rfl
  | step _ _ ih=>simp only [List.length_cons,ih]

/-- The cut uses the same actual ordered prefix, with no journal event. -/
theorem Path.native (path : Path packets w a n items v) :
    (((packets.take n).mapM newTxSkb).run w).run a=.ok ((items,v),a) := by
  induction path with
  | zero=>rfl
  | step first tail ih=>
    simp only [List.take_succ_cons,List.mapM_cons,MaterialOrigin.bind_ok_ambient]
    exact ⟨_,_,_,first,_,_,_,ih,rfl⟩

/-- Each requested interior cut exists because newTxSkb is total with a
present device; no successful-prefix premise hides partial allocation. -/
theorem path_total (packets : List DataPacket) (device : w.dev=some d)
    (bound : n≤packets.length) : ∃ items v, Path packets w a n items v := by
  induction packets generalizing w d n with
  | nil=>
    have zero : n=0 := by simpa using bound
    subst n
    exact ⟨[],w,.zero⟩
  | cons packet packets ih=>
    cases n with
    | zero=>exact ⟨[],w,.zero⟩
    | succ n=>
      let next := {d with txSkbs:=d.txSkbs.insert d.nextSkb packet,nextSkb:=d.nextSkb+1}
      let u := Packets.update w (fun v=>{v with txSkbs:=v.txSkbs.insert d.nextSkb packet,nextSkb:=d.nextSkb+1})
      have atNext : u.dev=some next := by simp [u,next,Packets.update,device]
      obtain ⟨items,v,tail⟩ := ih atNext (Nat.le_of_succ_le_succ bound)
      exact ⟨d.nextSkb::items,v,.step (Packets.newTxSkb_run w a d packet device) tail⟩

/-- This is the fixed take/drop split of the original allocator, not a
user-supplied factorization. It exposes the continuation of each native cut. -/
theorem source_factor (packets : List DataPacket) (n : Nat) :
    packets.mapM newTxSkb=(do
      let prefixItems←(packets.take n).mapM newTxSkb
      let suffixItems←(packets.drop n).mapM newTxSkb
      pure (prefixItems++suffixItems) : WG.M (List SkbId)) := by
  calc
    packets.mapM newTxSkb = ((packets.take n)++(packets.drop n)).mapM newTxSkb := by
      rw [List.take_append_drop]
    _ = _ := List.mapM_append

/-- A completed whole allocation passes through this exact structural path;
the remaining native run starts at its actual saved cut world. -/
theorem Path.remaining (path : Path packets w a n items u)
    (complete : ((packets.mapM newTxSkb).run w).run a=.ok ((allItems,v),b)) :
    ∃ rest, (((packets.drop n).mapM newTxSkb).run u).run a=.ok ((rest,v),b) ∧
      allItems=items++rest := by
  rw [source_factor packets n,MaterialOrigin.bind_ok_ambient] at complete
  obtain ⟨prefixItems,cut,clock,first,tail⟩ := complete
  rw [path.native] at first
  cases first
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨rest,last,lastClock,remaining,done⟩ := tail
  cases done
  exact ⟨rest,remaining,rfl⟩

theorem Path.silent (path : Path packets w a n items v) (history : List CausalJournal.Event) :
    runWGPrefix (liftWGPrefix ((packets.take n).mapM newTxSkb)) w a history=
      (.ok ((items,v),a),history) := by
  rw [runWGPrefix_lift,path.native]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
