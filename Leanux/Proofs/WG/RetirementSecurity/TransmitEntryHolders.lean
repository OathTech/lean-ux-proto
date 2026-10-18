import Leanux.Proofs.WG.RetirementSecurity.TransmitPendingHolders

/-! Full original transmit entry retains the actual key-holder account.
Its destination lookup supplies the peer protection needed by the final
payment, so callers do not assume release readiness at an invented boundary. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Std.Do
open Queues.RxCredits
namespace TransmitEntry

theorem finish (before : Pending temporary initial (some pid) w)
    (ps : List WG.Packet) (a b : Ambient)
    (run : ((Packets.txFinish pid ps).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := by
  simp only [Packets.txFinish,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,spliceRun,_,t,e,stageRun,_,s,f,putRun,done⟩ := run
  cases done
  have selected := (hoare_iff_run_ambient _ _ _).mp
    (pending_frame (splice pid ps)
      (reply_views (project := id) (xmitSplice_protect pid ps) (xmitSplice_keyView pid ps)) initial (some pid))
    w a () u c before spliceRun
  have accountT := selected.1.1.staged selected.1.2 (selected.2.1 pid) c e stageRun
  have pendingT := (hoare_iff_run_ambient _ _ _).mp (pending_stage initial pid)
    u c () t e selected.2 stageRun
  exact repay_keys accountT pendingT e b putRun

end TransmitEntry

/-- Every normal original wgXmit path preserves key-reference ownership,
including rejection after destination lookup. Successful lookup derives the
extra peer credit for selection and final payment; staging uses only the real
current-slot key acquisition. Packet boundedness and current affiliation
remain explicit independent caller invariants. -/
theorem HolderAccount.transmit (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (compatible : CurrentsCompatible w)
    (family addr : Nat) (ps : List WG.Packet) (mtu : Nat) (a b : Ambient)
    (run : ((wgXmit family addr ps mtu).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := by
  rw [Packets.wgXmit_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨checked,u,c,checkRun,tail⟩ := run
  have heldU := (hoare_iff_run_ambient _ _ _).mp (TransmitEntry.check family addr ps mtu)
    w a checked u c ⟨account,bounded⟩ checkRun
  have checkView := (ProjectedAction.iff_run_ambient _ _ _).mp
    (txCheck_reply family addr ps mtu) w a checked u c checkRun
  have compatibleU := currents_view (congrArg Prod.snd checkView) compatible
  cases checked with
  | false =>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact heldU.1
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨peer,t,e,lookupRun,chosen,s,f,selectRun,tail⟩ := tail
    have heldT := TransmitEntry.lookup heldU family addr c e lookupRun
    have pendingT := lookup_pending family addr compatibleU lookupRun
    have selected := (hoare_iff_run_ambient _ _ _).mp
      (TransmitEntry.select u family ps mtu peer) t e chosen s f ⟨heldT,pendingT⟩ selectRun
    cases chosen with
    | error err => cases tail; exact selected.1.1
    | ok pair =>
      obtain ⟨pid,packets⟩ := pair
      exact TransmitEntry.finish selected packets f b tail

end Leanux.Proofs.WG.RetirementSecurity
