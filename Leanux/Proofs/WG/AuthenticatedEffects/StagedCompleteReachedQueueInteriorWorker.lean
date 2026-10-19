import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueInteriorAccounts

/-! The original worker's successful peek/read path fixes the dequeue entry.
Its native setter point retains the actual selected local and original
crypted/DEAD continuation, without assuming completion succeeds. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier

def headPrefix (pid : PeerId) : PrefixM CausalJournal.Event (Option (List SkbId × DataPacket)) := do
  let first ← TxSelection.peek pid
  let go ← TxWorker.ready first
  if !go then return none
  let some items := first | CausalJournal.completionOps.step (invariant "unreachable")
  let some id := items.head? | CausalJournal.completionOps.step (invariant "an empty ring item")
  let head ← CausalJournal.completionOps.packet id
  pure (some (items,head))

def afterDrop (pid : PeerId) (items : List SkbId) (head : DataPacket) : PrefixM CausalJournal.Event Bool := do
  let flag ← CausalJournal.completionOps.step (branch .txCrypted (head.state==.crypted))
  selectedCallback pid (some ⟨items,head,flag⟩)

def afterHead (pid : PeerId) : Option (List SkbId × DataPacket) → PrefixM CausalJournal.Event Bool
  | none => pure false
  | some (items,head) => do CausalJournal.completionOps.drop pid items; afterDrop pid items head

theorem worker_head_factor (pid : PeerId) : CausalJournal.transmit pid=headPrefix pid >>= afterHead pid := by
  rw [worker_selection_factor]
  simp only [workerSelection,bodySelection,headPrefix,bind_assoc]
  congr 1
  funext first
  congr 1
  funext go
  cases go <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,pure_bind,selectedCallback,afterHead]
  cases first with
  | none => rfl
  | some items =>
    cases chosen : items.head? with
    | none => simp only [chosen]; rfl
    | some id =>
      simp only [chosen,bind_assoc]
      congr 1
      funext head
      simp only [afterReadSelection,afterDrop,afterHead,bind_assoc,pure_bind]

/-- Only a nonempty ready head reaches the actual dequeue setter. -/
def workerMutation (pid : PeerId) : PrefixM CausalJournal.Event (Option (Peer × Peer)) := do
  let selected ← headPrefix pid
  match selected with
  | none => pure none
  | some _ => return some (←dropMutation pid)

theorem worker_mutation_run
    (selected : runPrefix (headPrefix pid) w history=(.ok (some (items,head),u),middle))
    (device : u.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (workerMutation pid) w history=
      (.ok (some (p,p),{u with wg:=replacePeer u.wg d pid {p with txQueue:=p.txQueue.dropPeeked}}),
        middle++[readEvent pid p,readEvent pid p]) := by
  rw [workerMutation,runPrefix_bind,selected]
  dsimp only
  rw [runPrefix_bind,drop_mutation device resident]
  rfl

theorem worker_continuation
    (selected : runPrefix (headPrefix pid) w history=(.ok (some (items,head),u),middle))
    (device : u.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (CausalJournal.transmit pid) w history=
      runPrefix (do dropDue pid items (p,p); afterDrop pid items head)
        {u with wg:=replacePeer u.wg d pid {p with txQueue:=p.txQueue.dropPeeked}}
        (middle++[readEvent pid p,readEvent pid p]) := by
  rw [worker_head_factor,runPrefix_bind,selected]
  change runPrefix (CausalJournal.completionOps.drop pid items >>= fun _=>afterDrop pid items head) u middle=_
  rw [runPrefix_bind,drop_original_suffix device resident]
  rw [runPrefix_bind]

/-- The selected path supplies its earlier concrete read account and actual
cached queue contents. No assumption about the later send is used. -/
theorem selection_head
    (path : SelectionPath ledger locals pid w history picked v last) :
    ∃ u middle d p,
      runPrefix (headPrefix pid) w history=(.ok (some (picked.items,picked.head),u),middle) ∧
      Accounted middle ledger [] locals u.wg ∧ u.wg.dev=some d ∧ d.peers[pid]?=some p ∧
      p.txQueue.peeked=some picked.items := by
  cases path with
  | intro pw rw sw dw ph rh sh id initial peeked readied nonempty read beforeDrop removed afterDrop guarded afterGuard pending =>
    obtain ⟨atPeek,cached,_⟩ := TxSelection.peek_entry pid initial.entry peeked
    obtain ⟨atReady,same,_⟩ := TxWorker.ready_entry (some picked.items) atPeek readied
    obtain ⟨_,sameRead,_⟩ := TxWorker.packet_entry id atReady read
    have full := (TxSelection.drop_erases pid picked.items sw sh).symm.trans (congrArg Prod.fst removed)
    rw [Leanux.Proofs.Framing.liftWG_run] at full
    cases native : ((txDropSource pid).run sw.wg).run sw.ambient with
    | error stop => simp [native,Except.map] at full
    | ok out =>
      obtain ⟨⟨ignored,g⟩,ambient⟩ := out
      cases ignored
      obtain ⟨d,p,device,resident,_,_⟩ := txDrop_effect pid sw.ambient ambient native
      refine ⟨sw,sh,d,p,?_,beforeDrop,device,resident,?_⟩
      · unfold headPrefix
        rw [runPrefix_bind,peeked]
        dsimp only
        rw [runPrefix_bind,readied]
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,nonempty]
        rw [runPrefix_bind,read]
        rfl
      · apply cached p
        rw [←same,←sameRead]
        simp [peerAt,device,resident]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
