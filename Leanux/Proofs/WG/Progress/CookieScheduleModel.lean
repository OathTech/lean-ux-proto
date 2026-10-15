import Leanux.Proofs.WG.Progress.CookieActivationModel

/-! The supplied record stream and final projected state for a complete cookie-only receive schedule. Each reschedule and final stop carries an arbitrary eight-byte payload. No ambient records or trailing records are included. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

def control (yielded : Bool) (bytes : List UInt8) : HiddenRecord :=
  ⟨(cookieControlSite yielded).info.id, bytes⟩
def records (ys : List (List UInt8)) (stop : List UInt8) : List HiddenRecord :=
  ys.map (control true) ++ [control false stop]
theorem control_passive (y : Bool) (bytes : List UInt8) :
    HiddenSite.passive (control y bytes).site = false := by
  cases y <;> rfl
theorem drop_control (y : Bool) (bytes : List UInt8) (rest : List HiddenRecord) :
    (control y bytes :: rest).dropWhile (fun r => HiddenSite.passive r.site) = control y bytes :: rest := by
  simp only [List.dropWhile_cons, control_passive, Bool.false_eq_true, ite_false]
theorem read_control (y : Bool) (bytes : List UInt8) (rest : List HiddenRecord)
    (len : bytes.length = 8) :
    resolveCookieRead y (control y bytes :: rest) = .ok (bytes,rest) := by
  unfold resolveCookieRead
  rw [drop_control]
  cases y <;> simp [control, cookieControlSite, HiddenSite.info,
    Worker.sectionId, Worker.index, len,
    List.take_of_length_le (by omega : bytes.length ≤ 8),
    List.drop_eq_nil_of_le (by omega : bytes.length ≤ 8)]
theorem records_drop (ys : List (List UInt8)) (stop : List UInt8) :
    (records ys stop).dropWhile (fun r => HiddenSite.passive r.site) = records ys stop := by
  cases ys <;> simp only [records, List.map_nil, List.nil_append, List.map_cons, List.cons_append, drop_control]
theorem resolve_stop (count : Nat) (stop : List UInt8) (len : stop.length = 8) :
    resolveCookieActivation count (records [] stop) = .ok ⟨count,false,[]⟩ := by
  induction count with
  | zero => simp [resolveCookieActivation, records, read_control false stop [] len]
  | succ count ih =>
    have resched : cookieReschedResult (records [] stop) = .ok (false, records [] stop) := by
      unfold cookieReschedResult cookieNext
      rw [records_drop]
      simp [records, control, cookieControlSite, HiddenSite.info, Worker.sectionId, Worker.index]
    simp [resolveCookieActivation, resched, cookieIncrement, ih, Except.map]
theorem resolve_yield (count : Nat) (bytes : List UInt8) (ys : List (List UInt8))
    (stop : List UInt8) (len : bytes.length = 8) :
    resolveCookieActivation (count+1) (records (bytes::ys) stop) =
      .ok ⟨1,true,records ys stop⟩ := by
  have next : cookieNext (records (bytes::ys) stop) = some HiddenSite.reschedReceive.info.id := by
    unfold cookieNext
    rw [records_drop]
    simp [records, control, cookieControlSite]
  simp only [resolveCookieActivation, cookieReschedResult, next, ite_true, records_drop]
  have read := read_control true bytes (records ys stop) len
  change resolveCookieRead true (records (bytes::ys) stop) = _ at read
  rw [read]

theorem activation_ne_self (a : Activation) : (a != a) = false := by
  rcases a with ⟨worker,pid,iterations⟩
  cases worker <;> change (!(pid == pid && iterations == iterations)) = false <;> simp

def finishedSnapshot (d : Device) (entry : Campaign2.Snapshot) : Campaign2.Snapshot :=
  {entry with
    wg := {entry.wg with device := some {d with
      handshakeQueue := []
      handshakeQueueLen := d.handshakeQueueLen-d.handshakeQueue.length}}
    ambient := {entry.ambient with
      hidden := some []
      suspended := []
      steps := (cookieProcessedSteps entry.ambient.netRxSection d.handshakeQueue.length
        entry.ambient.steps).push {decision := .workerConsumed, outcome := false, netRx := entry.ambient.netRxSection}}}

end Leanux.Proofs.WG.Progress.CookieFull
