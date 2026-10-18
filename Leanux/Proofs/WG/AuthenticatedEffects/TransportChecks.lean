import Leanux.Proofs.WG.AuthenticatedEffects.TransportAuthenticatedEntry
import Leanux.Proofs.WG.Packets.PublicationWorkers

/-! Positional pre-consume authentication certificates carried beside the
existing owner/publication invariant. This layer reuses its established state
proofs and adds checks only where the original poll emits replay receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportChecks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
variable {id : SkbId}

def Checked (pre : List RxHistory.Event) : RxHistory.Event → Prop
  | .checkedCounter _ id stamp pkt r => TransportAuthenticatedEntry.Certified pre id stamp pkt r
  | _ => True

def Safe (h : List RxHistory.Event) : Prop :=
  ∀ pre e post, h = pre ++ e :: post → Checked pre e

def Inv (h : List RxHistory.Event) (w : World) := PublicationJoint.Inv h w ∧ Safe h
abbrev Preserves (g : RxHistory.Obs α) := PrefixPreserves Inv Safe g

def sensitive : RxHistory.Event → Option Unit
  | .checkedCounter .. => some ()
  | _ => none

theorem Certified_append (hi : TransportAuthenticatedEntry.Certified h id stamp pkt r)
    (suffix : List RxHistory.Event) :
    TransportAuthenticatedEntry.Certified (h ++ suffix) id stamp pkt r :=
  ⟨hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.append suffix⟩

theorem Safe.append (hh : Safe h)
    (hs : ∀ pre e post, s = pre ++ e :: post → Checked (h ++ pre) e) : Safe (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s hh hs

theorem Safe.quiet (hh : Safe h) (hs : s.filterMap sensitive = []) : Safe (h ++ s) := by
  apply hh.append
  intro pre e post position
  cases e <;> try trivial
  case checkedCounter occurrence id stamp pkt r =>
    have member : RxHistory.Event.checkedCounter occurrence id stamp pkt r ∈ s := by rw [position]; simp
    have found : () ∈ s.filterMap sensitive := List.mem_filterMap.mpr ⟨_,member,rfl⟩
    simp [hs] at found

/-- Reuse the unchanged established invariant for exactly this run; only the
new positional certificate is additional. The stopped prefix is retained. -/
theorem combine (g : RxHistory.Obs α) (state : PublicationJoint.Preserves g)
    (checks : ∀ w h, Inv h w → Safe (runPrefix g w h).2) : Preserves g := by
  intro w h hi
  obtain ⟨s,hs,_,post⟩ := state w h hi.1
  have safe := checks w h hi
  refine ⟨s,hs,safe,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact ⟨by simpa only [hr] using post,safe⟩

theorem quiet (g : RxHistory.Obs α) (state : PublicationJoint.Preserves g)
    (frame : HistoryFrame sensitive g) : Preserves g := by
  apply combine g state
  intro w h hi
  obtain ⟨s,hs,_,_⟩ := state w h hi.1
  have projection := frame w h
  rw [hs,List.filterMap_append] at projection
  have empty : s.filterMap sensitive = [] := by simpa using projection
  rw [hs]
  exact hi.2.quiet empty

/-- Add the certificate history to an existing result-dependent native
contract without weakening its input or losing its returned witness. -/
theorem quiet_ensures (g : RxHistory.Obs α) (contract : PrefixEnsures P S g Q)
    (frame : HistoryFrame sensitive g) :
    PrefixEnsures (fun h w => P h w ∧ Safe h) Safe g
      (fun x h w => Q x h w ∧ Safe h) := by
  intro w h hi
  obtain ⟨s,hs,_,post⟩ := contract w h hi.1
  have projection := frame w h
  rw [hs,List.filterMap_append] at projection
  have empty : s.filterMap sensitive = [] := by simpa using projection
  have safe : Safe (runPrefix g w h).2 := hs ▸ hi.2.quiet empty
  refine ⟨s,hs,safe,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact ⟨by simpa only [hr] using post,safe⟩

theorem store (h : List RxHistory.Event) (w v : World)
    (eq : productStoreView v = productStoreView w) (hi : Inv h w) : Inv h v :=
  ⟨PublicationJoint.store h w v eq hi.1,hi.2⟩

theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) : Preserves (liftPrefix a) :=
  quiet _ (PublicationJoint.lift_store a frame) (HistoryFrame.lift _ a)

theorem mixed (a : PrefixM LifetimeEvent α)
    (state : PublicationJoint.Preserves (RxHistory.mixed a)) : Preserves (RxHistory.mixed a) :=
  quiet _ state ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
    sensitive (fun _ => rfl) a)

theorem audit (a : AuditM α)
    (state : PublicationJoint.Preserves (RxHistory.audit a)) : Preserves (RxHistory.audit a) :=
  quiet _ state (fun w h => focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent sensitive (fun _ => rfl) a w h)

theorem poll (pid : PeerId) (budget : Nat) : Preserves (RxHistory.observePoll pid budget) := by
  apply combine _ (PublicationJoint.poll pid budget)
  intro w h hi
  obtain ⟨suffix,run,certified⟩ := TransportAuthenticatedEntry.observePoll pid budget w h hi.1.2.1.1
  rw [run]
  apply hi.2.append
  intro pre e post position
  cases e <;> try trivial
  case checkedCounter occurrence id stamp pkt r =>
    have member : RxHistory.Event.checkedCounter occurrence id stamp pkt r ∈ suffix.map RxHistory.promote := by
      rw [position]; simp
    obtain ⟨joint,hm,equal⟩ := List.mem_map.mp member
    cases joint <;> simp only [RxHistory.promote] at equal <;> cases equal
    exact Certified_append (certified occurrence id stamp pkt r hm) pre

theorem initial (net bare : Bool) (w : World)
    (hw : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  refine ⟨PublicationJoint.initial net bare w hw,?_⟩
  intro pre e post impossible
  have length := congrArg List.length impossible
  simp at length

end Leanux.Proofs.WG.AuthenticatedEffects.TransportChecks
