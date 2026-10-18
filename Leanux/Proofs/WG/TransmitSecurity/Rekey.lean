import Leanux.Proofs.WG.TransmitSecurity.NonceFrames
import Leanux.Proofs.Logged.NativeCapture

/-! The native rekey trigger requests handshake work. Queueing and transmission
remain subject to sendQueuedHandshakeInitiation's own guards. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Rekey
open Leanux Leanux.WG Leanux.Proofs.Logged CounterWindow

def test (pid : PeerId) : WG.M Bool := do
  let current := (← getPeer pid).keypairCurrent
  let send ← WG.andM (branch .freshKeypair current.isSome) do
    let some id := current | invariant "unreachable"
    let k ← getKeypair id
    WG.andM (branch .freshValid k.sending.isValid) do
      WG.orM (branchCmp .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES)
        k.sendingCounter REKEY_AFTER_MESSAGES) do
        WG.andM (branch .freshInitiator k.iAmTheInitiator) do
          branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME
  branch .freshSend send

theorem factor (pid : PeerId) : keepKeyFresh pid = (do
    if ← test pid then sendQueuedHandshakeInitiation pid false) := by
  simp only [keepKeyFresh,test,bind_assoc]
  rfl

def countChecked (a : Ambient) (k : Keypair) : Ambient :=
  record (recordCmp (record (record a .freshKeypair true) .freshValid true)
    .freshCounter true k.sendingCounter REKEY_AFTER_MESSAGES) .freshSend true

theorem count_trigger (pid : PeerId) (slot : KeypairId) (p : Peer) (k : Keypair)
    (w : WGWorld) (d : Device) (a : Ambient)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (current : p.keypairCurrent = some slot) (key : d.keypairs[slot]? = some k)
    (valid : k.sending.isValid = true) (past : REKEY_AFTER_MESSAGES < k.sendingCounter) :
    ((test pid).run w).run a = .ok ((true,w),countChecked a k) := by
  simp [test,getPeer,getKeypair,getDev,device,peer,current,key,WG.andM,WG.orM,
    branch,branchCmp,AmbientM.branch,AmbientM.branchCmp,valid,past,countChecked,record,recordCmp]

def ageEntry (a : Ambient) (k : Keypair) : Ambient :=
  record (recordCmp (record (record a .freshKeypair true) .freshValid true)
    .freshCounter false k.sendingCounter REKEY_AFTER_MESSAGES) .freshInitiator true

theorem age_trigger (pid : PeerId) (slot : KeypairId) (p : Peer) (k : Keypair)
    (w : WGWorld) (d : Device) (a b : Ambient)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (current : p.keypairCurrent = some slot) (key : d.keypairs[slot]? = some k)
    (valid : k.sending.isValid = true) (count : k.sendingCounter ≤ REKEY_AFTER_MESSAGES)
    (initiator : k.iAmTheInitiator = true)
    (expired : ((branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME).run w).run
      (ageEntry a k) = .ok ((true,w),b)) :
    ((test pid).run w).run a = .ok ((true,w),record b .freshSend true) := by
  have notPast : ¬ k.sendingCounter > REKEY_AFTER_MESSAGES := Nat.not_lt.mpr count
  simp [test,getPeer,getKeypair,getDev,device,peer,current,key,WG.andM,WG.orM,
    branch,branchCmp,AmbientM.branch,AmbientM.branchCmp,valid,notPast,initiator]
  change ((branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME).run w).run
    (ageEntry a k) >>= (fun out => .ok ((out.1.1,out.1.2),record out.2 .freshSend out.1.1)) = _
  rw [expired]
  rfl

structure Request where
  peer : PeerId
  decision : WGRunWitness Bool

def Request.Valid (r : Request) : Prop :=
  r.decision.Valid (test r.peer) ∧ r.decision.value = true

def observe (pid : PeerId) : WGPrefix Request Unit := do
  let decision ← captureWGRun (test pid)
  if decision.value then
    emitStatePrefix ⟨pid,decision⟩
    liftWGPrefix (sendQueuedHandshakeInitiation pid false)

theorem observe_run (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Request) :
    runWGPrefix (observe pid) w a h =
      match ((test pid).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((false,v),b) => (.ok (((),v),b),h)
      | .ok ((true,v),b) =>
        (((sendQueuedHandshakeInitiation pid false).run v).run b,
          h ++ [⟨pid,⟨true,w,v,a,b⟩⟩]) := by
  unfold observe
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have captured := runWGPrefix_captureWGRun (E := Request) (test pid) w a h
  change runStatePrefix _ w a h = _ at captured
  rw [captured]
  cases hr : ((test pid).run w).run a with
  | error stop => rfl
  | ok out =>
    rcases out with ⟨⟨decision,v⟩,b⟩
    cases decision <;> rfl

theorem observe_erases (pid : PeerId) : ErasesStatePrefix (observe pid) (keepKeyFresh pid) := by
  rw [factor]
  intro w a h
  change (runWGPrefix (observe pid) w a h).1 = _
  rw [observe_run]
  simp only [StateT.run_bind]
  cases run : ((test pid).run w).run a with
  | error stop => rfl
  | ok out => rcases out with ⟨⟨decision,v⟩,b⟩; cases decision <;> rfl

theorem count_request (pid : PeerId) (slot : KeypairId) (p : Peer) (k : Keypair)
    (w : WGWorld) (d : Device) (a : Ambient) (h : List Request)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (current : p.keypairCurrent = some slot) (key : d.keypairs[slot]? = some k)
    (valid : k.sending.isValid = true) (past : REKEY_AFTER_MESSAGES < k.sendingCounter) :
    runWGPrefix (observe pid) w a h =
      (((sendQueuedHandshakeInitiation pid false).run w).run (countChecked a k),
        h ++ [⟨pid,⟨true,w,w,a,countChecked a k⟩⟩]) := by
  rw [observe_run,count_trigger pid slot p k w d a device peer current key valid past]


theorem age_request (pid : PeerId) (slot : KeypairId) (p : Peer) (k : Keypair)
    (w : WGWorld) (d : Device) (a b : Ambient) (h : List Request)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (current : p.keypairCurrent = some slot) (key : d.keypairs[slot]? = some k)
    (valid : k.sending.isValid = true) (count : k.sendingCounter ≤ REKEY_AFTER_MESSAGES)
    (initiator : k.iAmTheInitiator = true)
    (expired : ((branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME).run w).run
      (ageEntry a k) = .ok ((true,w),b)) :
    runWGPrefix (observe pid) w a h =
      (((sendQueuedHandshakeInitiation pid false).run w).run (record b .freshSend true),
        h ++ [⟨pid,⟨true,w,w,a,record b .freshSend true⟩⟩]) := by
  rw [observe_run,age_trigger pid slot p k w d a b device peer current key valid count initiator expired]

theorem observe_receipts (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Request) :
    ∃ suffix, (runWGPrefix (observe pid) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.peer = pid ∧ r.Valid := by
  rw [observe_run]
  cases decision : ((test pid).run w).run a with
  | error stop => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    cases result with
    | false => exact ⟨[],by simp⟩
    | true =>
      refine ⟨[⟨pid,⟨true,w,v,a,b⟩⟩],rfl,by simp,?_⟩
      intro r member
      have same := List.mem_singleton.mp member
      subst r
      exact ⟨rfl,decision,rfl⟩

end Leanux.Proofs.WG.TransmitSecurity.Rekey
