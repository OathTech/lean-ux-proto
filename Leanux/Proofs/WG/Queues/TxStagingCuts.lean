import Leanux.Proofs.WG.Queues.TxLogicalSelection
import Leanux.Proofs.WG.Packets.TxFront
import Leanux.Proofs.Logged.NativeCapture

/-! Exact adjacent allocation/create receipts from the original staged source.
A normal receipt retains both actual WG and Ambient boundaries. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.StagingCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes RxCredits

structure Receipt where
  peer : PeerId
  packets : List DataPacket
  allocation : WGRunWitness (List SkbId)
  creation : WGRunWitness Unit

def Receipt.Valid (r : Receipt) : Prop :=
  r.allocation.Valid (r.packets.mapM newTxSkb) ∧
  r.creation.Valid (createData r.peer r.allocation.value) ∧
  r.creation.before=r.allocation.after ∧
  r.creation.ambientBefore=r.allocation.ambientAfter

def allocateCreate (pid : PeerId) (packets : List DataPacket) : WG.M Unit := do
  let item ← packets.mapM newTxSkb
  createData pid item

def submit (pid : PeerId) (packets : List DataPacket) : WGPrefix Receipt Unit := do
  let allocation ← captureWGRun (packets.mapM newTxSkb)
  let creation ← captureWGRun (createData pid allocation.value)
  emitStatePrefix ⟨pid,packets,allocation,creation⟩

def Good (h : List Receipt) : Prop := ∀r∈h,r.Valid

theorem submit_run (pid : PeerId) (packets : List DataPacket)
    (w : WGWorld) (ambient : Ambient) (h : List Receipt) :
    runWGPrefix (submit pid packets) w ambient h =
      match ((packets.mapM newTxSkb).run w).run ambient with
      | .error stop => (.error stop,h)
      | .ok ((item,u),clock) =>
        match ((createData pid item).run u).run clock with
        | .error stop => (.error stop,h)
        | .ok (((),v),after) =>
          (.ok (((),v),after),h++[⟨pid,packets,⟨item,w,u,ambient,clock⟩,⟨(),u,v,clock,after⟩⟩]) := by
  change runStatePrefix (submit pid packets) w ambient h = _
  rw [submit,runStatePrefix_bind]
  have start := runWGPrefix_captureWGRun (E:=Receipt) (packets.mapM newTxSkb) w ambient h
  simp only [runWGPrefix] at start
  rw [start]
  cases allocated : ((packets.mapM newTxSkb).run w).run ambient with
  | error stop=>rfl
  | ok out=>
    rcases out with ⟨⟨item,u⟩,clock⟩
    simp only [Except.map]
    rw [runStatePrefix_bind]
    have next := runWGPrefix_captureWGRun (E:=Receipt) (createData pid item) u clock h
    simp only [runWGPrefix] at next
    rw [next]
    cases created : ((createData pid item).run u).run clock with
    | error stop=>rfl
    | ok out=>rcases out with ⟨⟨result,v⟩,after⟩; cases result; rfl

theorem submit_erases (pid : PeerId) (packets : List DataPacket) :
    ErasesStatePrefix (submit pid packets) (allocateCreate pid packets) := by
  intro w ambient h
  change (runWGPrefix (submit pid packets) w ambient h).1 = _
  rw [submit_run]
  unfold allocateCreate
  cases allocated : ((packets.mapM newTxSkb).run w).run ambient with
  | error stop=>simp only [StateT.run_bind,allocated]; rfl
  | ok out=>
    rcases out with ⟨⟨item,u⟩,clock⟩
    simp only [StateT.run_bind,allocated]
    change _ = ((createData pid item).run u).run clock
    cases created : ((createData pid item).run u).run clock with
    | error stop=>rfl
    | ok out=>rcases out with ⟨⟨result,v⟩,after⟩; cases result; rfl

/-- A receipt is emitted only after both adjacent original calls return.
If either Stops, the prior journal survives without a fabricated endpoint. -/
theorem submit_safe (pid : PeerId) (packets : List DataPacket) :
    StatePrefixPreserves (fun h _ _=>Good h) Good (submit pid packets) := by
  intro w ambient h hi
  have run := submit_run pid packets w ambient h
  simp only [runWGPrefix,runStatePrefix] at run
  rw [run]
  cases allocated : ((packets.mapM newTxSkb).run w).run ambient with
  | error stop=>exact ⟨[],by simp,hi,True.intro⟩
  | ok out=>
    rcases out with ⟨⟨item,u⟩,clock⟩
    dsimp only
    cases created : ((createData pid item).run u).run clock with
    | error stop=>exact ⟨[],by simp,hi,True.intro⟩
    | ok out=>
      rcases out with ⟨⟨result,v⟩,after⟩
      cases result
      let receipt : Receipt := ⟨pid,packets,⟨item,w,u,ambient,clock⟩,⟨(),u,v,clock,after⟩⟩
      have valid : receipt.Valid := ⟨allocated,created,rfl,rfl⟩
      have good : Good (h++[receipt]) := by
        intro r member
        rcases List.mem_append.mp member with old | added
        · exact hi r old
        · have same : r=receipt := by simpa only [List.mem_singleton] using added
          exact same.symm ▸ valid
      exact ⟨[receipt],rfl,good,good⟩


def key (pid kid : Nat) (packets : List WG.Packet) : WGPrefix Receipt Unit := do
  let k ← liftWGPrefix (getKeypair kid)
  if ← liftWGPrefix (branch .stagedKeyInvalid !k.sending.isValid) then
    return ← liftWGPrefix (stagedOutNokey pid packets (some kid) false)
  if ← liftWGPrefix (branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME) then
    return ← liftWGPrefix (stagedOutNokey pid packets (some kid) true)
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← liftWGPrefix (branch .stagedNonceIterate true)
    let ds ← liftWGPrefix (ipTunnelEcnEncap pkt)
    let k ← liftWGPrefix (getKeypair kid)
    let nonce := k.sendingCounter
    liftWGPrefix (setKeypair kid {k with sendingCounter:=k.sendingCounter+1})
    if ← liftWGPrefix (branchCmp .stagedNonceRejected (nonce≥REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then
      return ← liftWGPrefix (stagedOutNokey pid packets (some kid) true)
    packetsCb := packetsCb++[{peer:=pid,keypair:=kid,nonce,plaintext:=pkt,ds}]
  _ ← liftWGPrefix (branch .stagedNonceIterate false)
  liftWGPrefix (Affiliation.sendAcquire kid)
  submit pid packetsCb

def staging (pid : PeerId) : WGPrefix Receipt Unit := do
  let p ← liftWGPrefix (getPeer pid)
  if ← liftWGPrefix (branch .stagedEmpty p.staged.isEmpty) then return
  liftWGPrefix (setPeer pid {p with staged:=[]})
  let kp ← liftWGPrefix (keypairGet p.keypairCurrent)
  if ← liftWGPrefix (branch .stagedNoKeypair kp.isNone) then
    return ← liftWGPrefix (stagedOutNokey pid p.staged kp false)
  let some kid := kp | liftWGPrefix (invariant "unreachable")
  key pid kid p.staged

theorem key_erases (pid kid : Nat) (packets : List WG.Packet) :
    ErasesStatePrefix (key pid kid packets) (stagedKeySource pid kid packets) := by
  unfold key stagedKeySource stagedSubmit
  repeat' first
    | exact submit_erases _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem staging_erases (pid : PeerId) :
    ErasesStatePrefix (staging pid) (sendStagedPackets pid) := by
  rw [←stagedFullSource_eq]
  unfold staging stagedFullSource
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro empty
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro ignored
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro kp
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro missing
    split
    · exact erasesStatePrefix_lift _
    · cases kp with
      | none=>exact erasesStatePrefix_lift _
      | some kid=>exact key_erases pid kid p.staged

private theorem lift_good (action : WG.M α) :
    StatePrefixPreserves (fun h _ _=>Good h) Good (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ hi=>hi) (fun _ _ _ _ _ _ hi _=>hi)

private theorem pure_good (x : α) :
    StatePrefixPreserves (fun h _ _=>Good h) Good (pure x : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi=>hi) (fun _ _ _ hi=>hi)

private theorem bind_good (a : WGPrefix Receipt α) (f : α→WGPrefix Receipt β)
    (ha : StatePrefixPreserves (fun h _ _=>Good h) Good a)
    (hf : ∀x,StatePrefixPreserves (fun h _ _=>Good h) Good (f x)) :
    StatePrefixPreserves (fun h _ _=>Good h) Good (a>>=f) :=
  StatePrefixEnsures.bind ha hf

private theorem forIn_good (xs : List α) (initial : β)
    (body : α→β→WGPrefix Receipt (ForInStep β))
    (keeps : ∀x b,StatePrefixPreserves (fun h _ _=>Good h) Good (body x b)) :
    StatePrefixPreserves (fun h _ _=>Good h) Good (forIn xs initial body) :=
  by
    induction xs generalizing initial with
    | nil=>exact pure_good _
    | cons x xs ih=>
      rw [List.forIn_cons]
      apply bind_good _ _ (keeps x initial)
      intro step
      cases step with
      | done b=>exact pure_good _
      | yield b=>exact ih b

theorem key_safe (pid kid : Nat) (packets : List WG.Packet) :
    StatePrefixPreserves (fun h _ _=>Good h) Good (key pid kid packets) := by
  unfold key
  repeat' first
    | exact submit_safe _ _
    | exact lift_good _
    | with_reducible exact pure_good _
    | with_reducible apply forIn_good
    | with_reducible apply bind_good
    | split
    | (with_reducible intro x; try dsimp only)

theorem staging_safe (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>Good h) Good (staging pid) := by
  unfold staging
  apply bind_good _ _ (lift_good _)
  intro p
  apply bind_good _ _ (lift_good _)
  intro empty
  split
  · exact pure_good _
  · apply bind_good _ _ (lift_good _)
    intro ignored
    apply bind_good _ _ (lift_good _)
    intro kp
    apply bind_good _ _ (lift_good _)
    intro missing
    split
    · exact lift_good _
    · cases kp with
      | none=>exact lift_good _
      | some kid=>exact key_safe pid kid p.staged


/-- The original native front and payment wrap the captured staging source. -/
def transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) : WGPrefix Receipt Int := do
  match ← liftWGPrefix (Packets.txFront family addr packets mtu) with
  | .error err=>pure err
  | .ok pid=>
    staging pid
    liftWGPrefix (peerPut (some pid))
    pure 0

theorem transmit_erases (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    ErasesStatePrefix (transmit family addr packets mtu) (wgXmit family addr packets mtu) := by
  rw [Packets.wgXmit_front_factor]
  unfold transmit
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro outcome
  cases outcome with
  | error err=>exact erasesStatePrefix_pure _
  | ok pid=>
    unfold Packets.txTail
    apply erasesStatePrefix_bind (staging_erases pid)
    intro ignored
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro ignored
    exact erasesStatePrefix_pure _

theorem transmit_safe (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    StatePrefixPreserves (fun h _ _=>Good h) Good (transmit family addr packets mtu) := by
  unfold transmit
  apply bind_good _ _ (lift_good _)
  intro outcome
  cases outcome with
  | error err=>exact pure_good _
  | ok pid=>
    apply bind_good _ _ (staging_safe pid)
    intro ignored
    apply bind_good _ _ (lift_good _)
    intro ignored
    exact pure_good _

/-- The two captured calls are adjacent in both state components. -/
theorem Receipt.joined {r : Receipt} (valid : r.Valid) :
    (((do let item←r.packets.mapM newTxSkb; createData r.peer item; pure item) :
      WG.M (List SkbId)).run r.allocation.before).run r.allocation.ambientBefore =
      .ok ((r.allocation.value,r.creation.after),r.creation.ambientAfter) := by
  have allocated := valid.1
  have created := valid.2.1
  unfold WGRunWitness.Valid at created
  rw [valid.2.2.1,valid.2.2.2] at created
  change ((r.packets.mapM newTxSkb).run r.allocation.before).run r.allocation.ambientBefore = _ at allocated
  change ((createData r.peer r.allocation.value).run r.allocation.after).run r.allocation.ambientAfter = _ at created
  change (((r.packets.mapM newTxSkb).run r.allocation.before).run r.allocation.ambientBefore >>= _) = _
  rw [allocated]
  change (((createData r.peer r.allocation.value).run r.allocation.after).run r.allocation.ambientAfter >>= _) = _
  rw [created]
  rfl

/-- A captured full-ring refusal derives its actual DEAD head and live-ring
exclusion from the earlier allocation frontier, not from a later worker state. -/
theorem Receipt.refusal {r : Receipt} {d : Device} {p : Peer}
    {first : SkbId} {rest : List SkbId} (valid : r.Valid)
    (device : r.allocation.before.dev=some d) (peer : d.peers[r.peer]?=some p)
    (live : p.isDead=false) (room : p.txQueue.count<MAX_QUEUED_PACKETS)
    (full : d.encryptQueue.full=true)
    (bounded : ∀old∈d.encryptQueue.items,∀id∈old,id<d.nextSkb)
    (item : r.allocation.value=first::rest) :
    HeadState first .dead r.creation.after ∧
      TxRing.nativeCell r.creation.after=some (d.ifindex,d.encryptQueue) ∧
      ∀old∈d.encryptQueue.items,first∉old := by
  have run := Receipt.joined valid
  rw [item] at run
  obtain ⟨_,head,ring,outside⟩ := LogicalSelection.allocated_refusal r.peer r.packets
    device peer live room full bounded run
  exact ⟨head,ring,outside⟩

end Leanux.Proofs.WG.Queues.TxDisposition.StagingCuts
