import Leanux.Proofs.WG.Packets.PublicationPollChecks
import Leanux.Proofs.WG.Packets.PublicationFrontier
import Leanux.Proofs.WG.Packets.PublicationFrontierPoll

/-! Positional consume certificates on the existing persistent receive journal.
The state conjunct also carries the packet-owner frontier used by allocation. -/
namespace Leanux.Proofs.WG.PublicationChecks
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

def Checked (pre : List RxHistory.Event) : RxHistory.Event → Prop
  | .consumed _ id stamp receipt => PublicationPollChecks.Certified pre id stamp receipt
  | _ => True

def Safe (h : List RxHistory.Event) : Prop :=
  ∀ pre e post, h = pre ++ e :: post → Checked pre e

def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  PublicationFrontier.Inv h w.wg ∧ Safe h

def sensitive : RxHistory.Event → Option Unit
  | .consumed .. => some ()
  | _ => none

abbrev Preserves (g : RxHistory.Obs α) := PrefixPreserves Inv Safe g

theorem Certified.append {id : SkbId} (hi : PublicationPollChecks.Certified h id stamp receipt)
    (suffix : List RxHistory.Event) : PublicationPollChecks.Certified (h ++ suffix) id stamp receipt := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,source,certificate⟩ := hi
  exact ⟨pre,post ++ suffix,r,out,pid,published,ambient,
    by simp only [position,List.append_assoc,List.cons_append],source,certificate⟩

theorem Safe.append (hh : Safe h)
    (hs : ∀ pre e post, s = pre ++ e :: post → Checked (h ++ pre) e) : Safe (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s hh hs

theorem Safe.quiet (hh : Safe h) (hs : s.filterMap sensitive = []) : Safe (h ++ s) := by
  apply hh.append
  intro pre e post position
  cases e <;> try trivial
  case consumed occurrence id stamp receipt =>
    have member : RxHistory.Event.consumed occurrence id stamp receipt ∈ s := by rw [position]; simp
    have found : () ∈ s.filterMap sensitive :=
      List.mem_filterMap.mpr ⟨_,member,rfl⟩
    simp [hs] at found

theorem Safe.of_unchanged (g : RxHistory.Obs α) (appends : Appends g)
    (frame : HistoryFrame sensitive g) (hi : Safe h) : Safe (runPrefix g w h).2 := by
  obtain ⟨suffix,hs⟩ := appends w h
  have projection := frame w h
  rw [hs,List.filterMap_append] at projection
  have empty : suffix.filterMap sensitive = [] := by simpa using projection
  rw [hs]
  exact hi.quiet empty

/-- State transport and positional checks refer to one exact observer run.
The state theorem may establish fresh anchors at actual publication events. -/
theorem combine (g : RxHistory.Obs α)
    (state : PrefixPreserves (fun h w => PublicationFrontier.Inv h w.wg) (fun _ => True) g)
    (checks : ∀ w h, Inv h w → Safe (runPrefix g w h).2) : Preserves g := by
  intro w h hi
  obtain ⟨suffix,hs,_,normal⟩ := state w h hi.1
  have safe := checks w h hi
  refine ⟨suffix,hs,safe,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact ⟨by simpa only [hr] using normal,safe⟩

theorem quiet_observed (g : RxHistory.Obs α) (appends : Appends g)
    (frame : HistoryFrame sensitive g)
    (state : PrefixPreserves (fun h w => PublicationFrontier.Inv h w.wg) (fun _ => True) g) :
    Preserves g :=
  combine g state (fun _ _ hi => Safe.of_unchanged g appends frame hi.2)

/-- An unchanged consumed-event projection preserves every old strict-prefix
certificate. Normal state transport uses the actual action at this input. -/
theorem quiet (g : RxHistory.Obs α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a) (frame : HistoryFrame sensitive g)
    (preserves : ∀ history, Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) a) :
    Preserves g := by
  intro w h hi
  obtain ⟨suffix,hs⟩ := appends w h
  have projection := frame w h
  rw [hs,List.filterMap_append] at projection
  have empty : suffix.filterMap sensitive = [] := by simpa using projection
  have safe : Safe (runPrefix g w h).2 := hs ▸ hi.2.quiet empty
  refine ⟨suffix,hs,safe,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    have state := (hoare_iff_run _ _ _).mp (preserves h) w out.1 out.2 hi.1
      ((erases w h).symm.trans hr)
    exact ⟨hs ▸ state.append suffix,safe⟩

/-- The actual poll's packet state is supplied by its normal native/product
contract; its event certificates are independently captured at each entry. -/
theorem poll (pid : PeerId) (budget : Nat)
    (frontier : ∀ history, Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (rxPoll pid budget (fun packets => packets.forM Env.deliverInner))) :
    Preserves (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨suffix,run,certified⟩ := PublicationPollChecks.observePoll_certificates pid budget w h hi.1.1
  have safe : Safe (h ++ suffix.map RxHistory.promote) := by
    apply hi.2.append
    intro pre e post position
    cases e <;> try trivial
    case consumed occurrence id stamp receipt =>
      have member : RxHistory.Event.consumed occurrence id stamp receipt ∈ suffix.map RxHistory.promote := by
        rw [position]; simp
      obtain ⟨joint,hm,equal⟩ := List.mem_map.mp member
      cases joint <;> simp only [RxHistory.promote] at equal <;> cases equal
      exact Certified.append (certified occurrence id stamp receipt hm) pre
  refine ⟨suffix.map RxHistory.promote,congrArg Prod.snd run,?_,?_⟩
  · simpa only [run] using safe
  · have erases := RxHistory.observePoll_erases pid budget w h
    cases hr : (runPrefix (RxHistory.observePoll pid budget) w h).1 with
    | error e => trivial
    | ok out =>
      have state := (hoare_iff_run _ _ _).mp (frontier h) w out.1 out.2 hi.1
        (erases.symm.trans hr)
      exact ⟨(congrArg Prod.snd run) ▸ state.append _,by simpa only [run] using safe⟩

/-- Both flags of the actual fixture start with no receive cells or consume
events. This is an initialization lemma, not a completed runner closure. -/
theorem initial (net bare : Bool) (w : World)
    (hw : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  refine ⟨PublicationFrontier.initial net bare w.wg hw,?_⟩
  intro pre e post impossible
  have length := congrArg List.length impossible
  simp only [List.length_nil,List.length_append,List.length_cons] at length
  omega

/-- The concrete Stack callback discharges the frontier contract of the
actual poll. The positional certificate still comes from its entry receipt. -/
theorem actual_poll (pid : PeerId) (budget : Nat) :
    Preserves (RxHistory.observePoll pid budget) :=
  poll pid budget (fun history => PublicationFrontier.poll_stack pid budget history)

end Leanux.Proofs.WG.PublicationChecks
