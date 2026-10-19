import Leanux.Proofs.WG.RetirementSecurity.TxActorHandshake
import Leanux.Proofs.WG.RetirementSecurity.TxActorScheduler

/-! Concrete source worker contracts close the native scheduler's iteration
premise. Actual dispatch, suspension, resumption, crypt-ahead and NAPI are
composed; no callback or iteration invariant is assumed by this local carrier
transport. Initialization and lifecycle joins remain distinct. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem native_iteration : IterationContract (Covered locals crypt) crypt := by
  intro act w result v before run
  cases worker:act.worker with
  | encryptWorker=>
    simp only [Env.Activation.iter,worker] at run
    simp only [actor,worker,Option.toList_none,ite_self] at before ⊢
    exact encrypt_iteration before run
  | decryptWorker=>
    simp only [Env.Activation.iter,worker] at run
    simp only [actor,worker,Option.toList_none,ite_self] at before ⊢
    exact (hoare_iff_run _ _ _).mp decrypt_iteration w result v before run
  | receiveWorker=>
    simp only [Env.Activation.iter,worker] at run
    simp only [actor,worker,Option.toList_none,ite_self] at before ⊢
    exact (hoare_iff_run _ _ _).mp handshake_iteration w result v before run
  | txWorker=>
    cases peer:act.pid with
    | none=>simp only [Env.Activation.iter,worker,peer] at run; cases run
    | some pid=>
      simp only [Env.Activation.iter,worker,peer] at run
      rw [MaterialOrigin.bind_ok] at run
      obtain ⟨_,u,ahead,stepped⟩:=run
      simp only [actor,worker,peer,Option.toList_some] at before ⊢
      exact transmit_iteration ((hoare_iff_run _ _ _).mp (crypt_ahead pid) w () u before ahead) stepped
  | sendWorker | netRx | timerRetransmit | timerSendKeepalive | timerNewHandshake | timerZeroKey |
      clearPeerWorker | timerPersistentKeepalive | netnsCleanup | linkwatch=>
    simp only [Env.Activation.iter,worker] at run
    cases run

theorem native_scheduler (stack : Option Worker) :
    Preserves (At (Covered locals crypt) crypt []) (Env.schedule stack) :=
  scheduler_service (fun pid=>covered_work (·.erase pid)) native_iteration napi_actor stack

end Leanux.Proofs.WG.RetirementSecurity.TxWork
