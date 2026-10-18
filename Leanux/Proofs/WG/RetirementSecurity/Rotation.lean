import Leanux.Proofs.WG.RetirementSecurity.Transfer
import Leanux.Proofs.WG.Queues.TxDisposition

/-! Slot insertion transfers the newly created/acquired caller occurrence
into the correct native slot and pays exactly the references displaced by
the source's initiator/responder branches. No distinctness of key slots is
assumed: the ledger counts reference occurrences, including aliases. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

def rotatedPeer (p : Peer) (newKey : KeypairId) (initiator : Bool) : Peer :=
  if initiator then
    if p.keypairNext.isSome then
      {p with keypairNext := none, keypairPrevious := p.keypairNext, keypairCurrent := some newKey}
    else {p with keypairPrevious := p.keypairCurrent, keypairCurrent := some newKey}
  else {p with keypairNext := some newKey, keypairPrevious := none}

def SlotLoans.rotate (loans : SlotLoans) (newKey : Credits.Allocation)
    (initiator hasNext : Bool) : SlotLoans :=
  if initiator then
    if hasNext then ⟨none,loans.next,some newKey⟩
    else ⟨loans.next,loans.current,some newKey⟩
  else ⟨some newKey,none,loans.current⟩

def rotationStart (pid : PeerId) (p : Peer) : WG.M Unit := do
  if ← branch .addKeypairHasNext p.keypairNext.isSome then
    updatePeer pid fun q => {q with keypairNext := none, keypairPrevious := p.keypairNext}
    keypairPut p.keypairCurrent true
  else
    updatePeer pid fun q => {q with keypairPrevious := p.keypairCurrent}

/-- The original insertion body after its peer/key getters and initiator
branch. The nested helper is definitionally the mirror's peer update. -/
def rotationBody (pid : PeerId) (newKey : KeypairId) (p : Peer) (initiator : Bool) : WG.M Unit := do
  if initiator then
    rotationStart pid p
    keypairPut p.keypairPrevious true
    updatePeer pid fun q => {q with keypairCurrent := some newKey}
  else
    updatePeer pid fun q => {q with keypairNext := some newKey}
    keypairPut p.keypairNext true
    updatePeer pid fun q => {q with keypairPrevious := none}
    keypairPut p.keypairPrevious true

theorem rotation_source (pid : PeerId) (newKey : KeypairId) :
    addNewKeypair pid newKey = (do
      let p ← getPeer pid
      let k ← getKeypair newKey
      let initiator ← branch .addKeypairInitiator k.iAmTheInitiator
      rotationBody pid newKey p initiator) := by
  simp only [addNewKeypair,rotationBody,rotationStart,bind_assoc,Queues.TxDisposition.bind_ite]
  rfl

theorem rotation_body_account (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (newKey : Credits.Allocation) (remaining : Credits.Ledger) (initiator : Bool)
    (aligned : loans.Aligned p) :
    Hoare (rotationBody pid newKey.slot p initiator)
      (PeerAccount pid p (newKey :: loans.credits ++ remaining))
      (fun _ => PeerAccount pid (rotatedPeer p newKey.slot initiator)
        ((loans.rotate newKey initiator p.keypairNext.isSome).credits ++ remaining)) := by
  cases initiator with
  | false =>
    have order : (newKey :: loans.credits ++ remaining).Perm
        (loans.next.toList ++ (loans.previous.toList ++ (newKey :: loans.current.toList ++ remaining))) := by
      apply List.perm_iff_count.mpr
      intro allocation
      simp only [SlotLoans.credits,List.count_append,List.count_cons]
      omega
    apply hoare_consequence (P := PeerAccount pid p
      (loans.next.toList ++ (loans.previous.toList ++ (newKey :: loans.current.toList ++ remaining)))) ?_
      (fun _ hi => hi.perm order) (fun _ _ hi => hi)
    simp only [rotationBody,rotatedPeer,SlotLoans.rotate,Bool.false_eq_true,↓reduceIte]
    apply hoare_bind _ _ (update_peer_account pid p _ (fun q => {q with keypairNext := some newKey.slot}))
    intro _
    have payNext := put_peer_account pid {p with keypairNext := some newKey.slot} loans.next
      (loans.previous.toList ++ (newKey :: loans.current.toList ++ remaining)) true
    rw [aligned.1] at payNext
    apply hoare_bind _ _ payNext
    intro _
    apply hoare_bind _ _ (update_peer_account pid {p with keypairNext := some newKey.slot} _
      (fun q => {q with keypairPrevious := none}))
    intro _
    have payPrevious := put_peer_account pid {p with keypairNext := some newKey.slot, keypairPrevious := none}
      loans.previous (newKey :: loans.current.toList ++ remaining) true
    rw [aligned.2.1] at payPrevious
    exact payPrevious
  | true =>
    cases hasNext : p.keypairNext.isSome with
    | false =>
      have peerNone : p.keypairNext = none := by
        cases cell : p.keypairNext with
        | none => rfl
        | some key => simp [cell] at hasNext
      have loanNone : loans.next = none := Option.map_eq_none_iff.mp (aligned.1.trans peerNone)
      have order : (newKey :: loans.credits ++ remaining).Perm
          (loans.previous.toList ++ (loans.current.toList ++ newKey :: remaining)) := by
        apply List.perm_iff_count.mpr
        intro allocation
        simp only [SlotLoans.credits,loanNone,Option.toList_none,List.nil_append,List.count_append,List.count_cons]
        omega
      apply hoare_consequence (P := PeerAccount pid p
        (loans.previous.toList ++ (loans.current.toList ++ newKey :: remaining))) ?_
        (fun _ hi => hi.perm order) (fun _ _ hi => hi)
      have start : Hoare (rotationStart pid p)
          (PeerAccount pid p (loans.previous.toList ++ (loans.current.toList ++ newKey :: remaining)))
          (fun _ => PeerAccount pid {p with keypairPrevious := p.keypairCurrent}
            (loans.previous.toList ++ (loans.current.toList ++ newKey :: remaining))) := by
        unfold rotationStart
        apply branch_bind
        simp only [hasNext,Bool.false_eq_true,↓reduceIte]
        exact update_peer_account pid p _ (fun q => {q with keypairPrevious := p.keypairCurrent})
      simp only [rotationBody,rotatedPeer,SlotLoans.rotate,hasNext,Bool.false_eq_true,↓reduceIte]
      apply hoare_bind _ _ start
      intro _
      have payPrevious := put_peer_account pid {p with keypairPrevious := p.keypairCurrent}
        loans.previous (loans.current.toList ++ newKey :: remaining) true
      rw [aligned.2.1] at payPrevious
      apply hoare_bind _ _ payPrevious
      intro _
      simpa only [SlotLoans.credits,loanNone,Option.toList_none,Option.toList_some,
        List.nil_append,List.append_assoc,List.singleton_append] using
        update_peer_account pid {p with keypairPrevious := p.keypairCurrent}
          (loans.current.toList ++ newKey :: remaining)
          (fun q => {q with keypairCurrent := some newKey.slot})
    | true =>
      have order : (newKey :: loans.credits ++ remaining).Perm
          (loans.current.toList ++ (loans.previous.toList ++ (loans.next.toList ++ newKey :: remaining))) := by
        apply List.perm_iff_count.mpr
        intro allocation
        simp only [SlotLoans.credits,List.count_append,List.count_cons]
        omega
      apply hoare_consequence (P := PeerAccount pid p
        (loans.current.toList ++ (loans.previous.toList ++ (loans.next.toList ++ newKey :: remaining)))) ?_
        (fun _ hi => hi.perm order) (fun _ _ hi => hi)
      have start : Hoare (rotationStart pid p)
          (PeerAccount pid p (loans.current.toList ++ (loans.previous.toList ++ (loans.next.toList ++ newKey :: remaining))))
          (fun _ => PeerAccount pid {p with keypairNext := none, keypairPrevious := p.keypairNext}
            (loans.previous.toList ++ (loans.next.toList ++ newKey :: remaining))) := by
        unfold rotationStart
        apply branch_bind
        simp only [hasNext,↓reduceIte]
        apply hoare_bind _ _ (update_peer_account pid p _
          (fun q => {q with keypairNext := none, keypairPrevious := p.keypairNext}))
        intro _
        have payCurrent := put_peer_account pid {p with keypairNext := none, keypairPrevious := p.keypairNext}
          loans.current (loans.previous.toList ++ (loans.next.toList ++ newKey :: remaining)) true
        rw [aligned.2.2] at payCurrent
        exact payCurrent
      simp only [rotationBody,rotatedPeer,SlotLoans.rotate,hasNext,↓reduceIte]
      apply hoare_bind _ _ start
      intro _
      have payPrevious := put_peer_account pid {p with keypairNext := none, keypairPrevious := p.keypairNext}
        loans.previous (loans.next.toList ++ newKey :: remaining) true
      rw [aligned.2.1] at payPrevious
      apply hoare_bind _ _ payPrevious
      intro _
      simpa only [SlotLoans.credits,Option.toList_none,Option.toList_some,List.nil_append,
        List.append_assoc,List.singleton_append] using
        update_peer_account pid {p with keypairNext := none, keypairPrevious := p.keypairNext}
          (loans.next.toList ++ newKey :: remaining)
          (fun q => {q with keypairCurrent := some newKey.slot})

theorem SlotLoans.rotate_aligned {loans : SlotLoans} {p : Peer}
    (aligned : loans.Aligned p) (newKey : Credits.Allocation) (initiator : Bool) :
    (loans.rotate newKey initiator p.keypairNext.isSome).Aligned
      (rotatedPeer p newKey.slot initiator) := by
  cases initiator with
  | false => exact ⟨rfl,rfl,aligned.2.2⟩
  | true =>
    cases flag : p.keypairNext.isSome with
    | false =>
      simpa only [SlotLoans.rotate,rotatedPeer,flag,Bool.false_eq_true,↓reduceIte,SlotLoans.Aligned] using
        (show loans.next.map (·.slot) = p.keypairNext ∧
          loans.current.map (·.slot) = p.keypairCurrent ∧
          (some newKey).map (·.slot) = some newKey.slot from ⟨aligned.1,aligned.2.2,rfl⟩)
    | true =>
      simpa only [SlotLoans.rotate,rotatedPeer,flag,↓reduceIte,SlotLoans.Aligned] using
        (show (none : Option Credits.Allocation).map (·.slot) = none ∧
          loans.next.map (·.slot) = p.keypairNext ∧
          (some newKey).map (·.slot) = some newKey.slot from ⟨rfl,aligned.1,rfl⟩)

/-- Original insertion selects its branch from the actual new key record,
then transfers and pays exactly the corresponding reference occurrences. -/
theorem rotation_account (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (newKey : Credits.Allocation) (remaining : Credits.Ledger) (k : Keypair)
    (aligned : loans.Aligned p)
    (account : PeerAccount pid p (newKey :: loans.credits ++ remaining) w)
    (resident : keyAt w newKey.slot = some k) (a b : Ambient)
    (run : ((addNewKeypair pid newKey.slot).run w).run a = .ok (((),v),b)) :
    PeerAccount pid (rotatedPeer p newKey.slot k.iAmTheInitiator)
      ((loans.rotate newKey k.iAmTheInitiator p.keypairNext.isSome).credits ++ remaining) v := by
  rw [rotation_source,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨readPeer,u,c,getPeerRun,run⟩ := run
  obtain ⟨worldSame,ambientSame,d,device,stored⟩ := Origins.getPeer_return pid w u readPeer a c getPeerRun
  subst u
  subst c
  have samePeer : readPeer = p := by
    have actual : peerAt w pid = some readPeer := by simp [peerAt,device,stored]
    exact Option.some.inj (actual.symm.trans account.1)
  subst readPeer
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨readKey,u,c,getKeyRun,run⟩ := run
  obtain ⟨worldSame,ambientSame,dev,hasDev,hasKey⟩ := KeyTimes.getKeypair_return newKey.slot w u readKey a c getKeyRun
  subst u
  subst c
  have sameKey : readKey = k := by
    have actual : keyAt w newKey.slot = some readKey := by simp [keyAt,hasDev,hasKey]
    exact Option.some.inj (actual.symm.trans resident)
  subst readKey
  have body := branch_bind .addKeypairInitiator k.iAmTheInitiator
    (PeerAccount pid p (newKey :: loans.credits ++ remaining))
    (rotationBody pid newKey.slot p) _ (rotation_body_account pid p loans newKey remaining k.iAmTheInitiator aligned)
  exact (hoare_iff_run_ambient _ _ _).mp body w a () v b account run

end Leanux.Proofs.WG.RetirementSecurity
