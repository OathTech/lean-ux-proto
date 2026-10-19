import Leanux.Proofs.WG.RetirementSecurity.TxWorkLifecycleFrames

/-! Literal native destructor cuts before the device allocation disappears.
The guard establishes no resident TX packets from converse coverage and
service, not from the R2 observer's logical identity-retirement events. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork.Destruct
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

def prepare : WG.M Unit := do
  modifyDev fun d=>{d with creatingNet:=false,incomingPort:=0}
  socketReinit none none
  peerRemoveAll

def check : WG.M Unit := do
  let d←getDev
  if !d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty then
    unsupported "wg_destruct with queued work (destroy_workqueue runs it)"
  if !d.handshakeQueue.empty then
    invariant "wg_destruct with handshake messages queued (wg_stop drains the ring)"

def settle : WG.M Unit := do
  mayHaveSlept
  modifyDev fun d=>{d with handshakeQueueLen:=0}
  mayHaveSlept
  ratelimiterUninit

def beforeReset : WG.M Unit := do
  prepare
  check
  settle

theorem factor : wgDestruct = (do
    beforeReset
    _root_.modify fun w:WGWorld=>{w with dev:=none}
    retireDeviceUnits) := by
  simp only [wgDestruct,beforeReset,prepare,check,settle,bind_assoc]
  congr 1
  funext _
  congr 1
  funext _
  congr 1
  funext _
  congr 1
  funext d
  split <;> split <;> simp only [bind_assoc,pure_bind]

theorem prepare_service : Preserves (Serving locals crypt tx) prepare := by
  unfold prepare
  repeat' first
    | (rx_retention_head socketReinit; exact serving_socket_reinit _ _)
    | (rx_retention_head peerRemoveAll; exact serving_remove_all)
    | serving_metadata_step

theorem check_empty (before : Serving [] [] [] w)
    (run : (check.run w).run a=.ok ((result,v),b)) :
    v=w ∧ TxDisposition.txPackets v=(fun _=>none) := by
  unfold check at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,u,c,read,tail⟩:=run
  obtain ⟨rfl,rfl,device⟩:=DecryptCarrier.getDev_current a c read
  by_cases busy : (!d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty)=true
  · simp only [busy,↓reduceIte,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,_,_,failed,_⟩:=tail
    cases failed
  · simp only [busy] at tail
    have empty:=busy
    have crypt : d.encryptQueue.empty=true := by
      simp only [Bool.or_eq_true] at empty
      cases found:d.encryptQueue.empty <;> simp_all
    have tx : d.txWorkQueue.isEmpty=true := by
      simp only [Bool.or_eq_true] at empty
      cases found:d.txWorkQueue.isEmpty <;> simp_all
    by_cases handshake : (!d.handshakeQueue.empty)=true
    · simp only [handshake,↓reduceIte] at tail
      cases tail
    · simp only [handshake] at tail
      cases tail
      exact ⟨rfl,guarded_no_packets before.1 before.2.2 before.2.1.2.2.physical device crypt tx⟩

theorem settle_wire : SameView txCryptWire settle := by
  intro initial
  change Preserves (fun w=>txCryptWire w=initial) _
  unfold settle
  repeat' first
    | (rx_retention_head mayHaveSlept; exact (cryptWire_store mayHaveSlept_sameWGStore).wp (·=initial))
    | (rx_retention_head ratelimiterUninit; exact limiter_wire.wp (·=initial))
    | crypt_wire_step initial

theorem before_reset_empty (before : Serving [] [] [] w)
    (run : (beforeReset.run w).run a=.ok (((),v),b)) :
    TxDisposition.txPackets v=(fun _=>none) := by
  simp only [beforeReset,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,front,_,s,e,checked,tail⟩:=run
  have ready:=(hoare_iff_run_ambient _ _ _).mp prepare_service w a () u c before front
  obtain ⟨_,empty⟩:=check_empty ready checked
  have same:=(ProjectedAction.iff_run_ambient _ _ _).mp settle_wire s e () v b tail
  exact (congrArg Prod.snd same).trans empty

/-- A successful native destructor reaches its actual device-reset statement
only after the checked source prefix has no resident TX allocation. The entry
service/coverage premise is explicit; it must come from the caller invariant. -/
theorem no_residual_reset (before : Serving [] [] [] w)
    (run : (wgDestruct.run w).run a=.ok (((),v),b)) :
    ∃u c,(beforeReset.run w).run a=.ok (((),u),c) ∧
      TxDisposition.txPackets u=(fun _=>none) ∧
      ((do _root_.modify fun g:WGWorld=>{g with dev:=none}; retireDeviceUnits : WG.M Unit).run u).run c=
        .ok (((),v),b) := by
  rw [factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨result,u,c,front,tail⟩:=run
  cases result
  exact ⟨u,c,front,before_reset_empty before front,tail⟩

end Leanux.Proofs.WG.RetirementSecurity.TxWork.Destruct
