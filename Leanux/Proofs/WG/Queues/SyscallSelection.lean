import Leanux.Proofs.WG.Queues.AdmissionSelection
import Leanux.Proofs.WG.Queues.SyscallEffects

/-! Admission queries through the existing syscall certificate. Entry resets,
seccomp decisions, descriptor ownership, and errno tails stay in the source
relation; only its admitted traffic subcertificate is selected. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SyscallSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AdmissionSelection ConservationEffects

def tail (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : ConservationSyscall.Checked loans dispatch)
    (hs : ConservationSyscall.Checked loans sendWorkers)
    (ht : ConservationSyscall.Checked loans timers)
    (hr : ConservationSyscall.Checked loans route)
    (hx : ConservationSyscall.Checked loans xmit)
    (ha : ConservationSyscall.Checked loans advance)
    (hc : ConservationSyscall.Checked loans cleanup) (query : Query hd.rule) :
    Query (ConservationSyscall.tail call hd hs ht hr hx ha hc).rule := by
  unfold ConservationSyscall.tail
  exact left hd.rule _ query

theorem tail_fates (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : ConservationSyscall.Checked loans dispatch)
    (hs : ConservationSyscall.Checked loans sendWorkers)
    (ht : ConservationSyscall.Checked loans timers)
    (hr : ConservationSyscall.Checked loans route)
    (hx : ConservationSyscall.Checked loans xmit)
    (ha : ConservationSyscall.Checked loans advance)
    (hc : ConservationSyscall.Checked loans cleanup) (query : Query hd.rule)
    (chosen : Fates query) (es : Conserves hs.rule) (et : Conserves ht.rule)
    (er : Conserves hr.rule) (ex : Conserves hx.rule)
    (ea : Conserves ha.rule) (ec : Conserves hc.rule) :
    Fates (tail call hd hs ht hr hx ha hc query) := by
  intro cs w h result v k final certificate c selected
  obtain ⟨ret,u,j,middle,front,rest⟩ :=
    SyscallEffects.tail_dispatch call hd hs ht hr hx ha hc es et er ex ea ec certificate
  rcases selected with ⟨ret',u',j',middle',front',_,selection⟩
  have same := (hd.rule.source front).symm.trans (hd.rule.source front')
  obtain ⟨rfl,rfl⟩ := same
  have ledgers := hd.rule.unique front front'
  subst middle'
  exact TrafficOccurrences.fate_continue (chosen front' selection) rest

macro "syscall_entry_query" query:term : tactic =>
  `(tactic| (
    unfold ConservationSyscall.entry
    apply right
    intro _
    apply right
    intro _
    apply right
    intro _
    apply right
    intro _
    first
      | exact $query
      | exact (AdmissionSelection.branch _ _ _ (never _) $query : Query _)))

def entry (call : Syscall) {body : RxHistory.Obs α}
    (hb : ConservationSyscall.Checked loans body) (query : Query hb.rule) :
    Query (ConservationSyscall.entry call hb).rule := by
  cases call
  case seccompInstall via flags filter len bad mode=>
    cases via <;> syscall_entry_query query
  all_goals syscall_entry_query query

macro "syscall_entry_query_fates" chosen:term : tactic =>
  `(tactic| (
    unfold entry
    apply right_fates
    intro _
    apply right_fates
    intro _
    apply right_fates
    intro _
    apply right_fates
    intro _
    first
      | exact AdmissionSelection.branch_fates _ _ _ (never _) _ (never_fates _) $chosen
      | exact $chosen))

theorem entry_fates (call : Syscall) {body : RxHistory.Obs α}
    (hb : ConservationSyscall.Checked loans body) (query : Query hb.rule)
    (chosen : Fates query) : Fates (entry call hb query) := by
  cases call
  case seccompInstall via flags filter len bad mode=>
    cases via <;> syscall_entry_query_fates chosen
  all_goals syscall_entry_query_fates chosen

def dispatch (call : Syscall) (index : Nat) : Query (ConservationSyscall.dispatch call).rule := by
  cases call
  case wgInject family port msg tos ll dest=>exact AdmissionSelection.injectDispatch family port msg tos ll dest
  case wgFlood count port family messages=>exact AdmissionSelection.flood count port family messages index
  case wgBatch items waitMs=>exact AdmissionSelection.batch items index
  all_goals exact never _

theorem dispatch_fates (call : Syscall) (index : Nat) : Fates (dispatch call index) := by
  cases call
  case wgInject family port msg tos ll dest=>exact injectDispatch_fates family port msg tos ll dest
  case wgFlood count port family messages=>exact flood_fates count port family messages index
  case wgBatch items waitMs=>exact batch_fates items index
  all_goals exact never_fates _

def mpr {action other : RxHistory.Obs α} (same : action=other)
    (types : ConservationSyscall.Checked loans action=ConservationSyscall.Checked loans other)
    (checked : ConservationSyscall.Checked loans other) (query : Query checked.rule) :
    Query (Eq.mpr types checked).rule := by
  cases same
  exact query

theorem mpr_fates {action other : RxHistory.Obs α} (same : action=other)
    (types : ConservationSyscall.Checked loans action=ConservationSyscall.Checked loans other)
    (checked : ConservationSyscall.Checked loans other) (query : Query checked.rule)
    (chosen : Fates query) : Fates (mpr same types checked query) := by
  cases same
  exact chosen

/-- This query is on the complete original syscall rule, including its
entry and return-to-user tail. The inner index selects the flood/batch item. -/
def syscall (call : Syscall) (index : Nat) : Query (ConservationSyscall.rule call) := by
  unfold ConservationSyscall.rule ConservationSyscall.syscall
  apply mpr (same:=Configuration.syscallRx_factor call)
  exact entry call _ (tail call _ _ _ _ _ _ _ (dispatch call index))

/-- A selected accepted occurrence is pending in this syscall's exact final
ledger or removed in its actual later suffix. This is independent of its errno. -/
theorem syscall_fates (call : Syscall) (index : Nat) : Fates (syscall call index) := by
  unfold syscall
  apply mpr_fates (same:=Configuration.syscallRx_factor call)
  apply entry_fates
  apply tail_fates
  · exact dispatch_fates call index
  · exact ConservationEffects.deferred _
  · exact ConservationEffects.idle
  · exact ConservationEffects.audit _
  · exact ConservationEffects.deferred _
  · exact ConservationEffects.deferred _
  · exact ConservationEffects.audit _

end Leanux.Proofs.WG.Queues.RxCredits.SyscallSelection
