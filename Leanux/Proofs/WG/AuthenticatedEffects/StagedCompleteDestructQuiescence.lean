import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetired
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerFrames

/-! The actual destructor guards discharge work and TX-queue quiescence.
The upper peer account and positive resident counts are explicitly supplied at
this local source cut, not silently inferred from initialized lower funding. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRetired
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open RetirementSecurity TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal
open Queues.RxCredits CompleteCarrier
variable {w v : WGWorld} {a b : Ambient} {holders : DurableHolders}
  {history : List Event} {ledger : Staged.Obligations.Ledger}

/-- These are the actual native guard facts; a missing device or queued work
cannot reach this normal return. -/
theorem check_fields (run : (TxWork.Destruct.check.run w).run a = .ok (((),v),b)) :
    v = w ∧ ∃ d, w.dev = some d ∧ d.sendWorkQueue = [] ∧ d.clearWorkQueue = [] ∧
      d.encryptQueue.empty = true ∧ d.txWorkQueue = [] := by
  unfold TxWork.Destruct.check at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,u,c,read,tail⟩ := run
  obtain ⟨rfl,rfl,device⟩ := DecryptCarrier.getDev_current a c read
  by_cases busy : (!d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty) = true
  · simp only [busy,↓reduceIte,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,_,_,failed,_⟩ := tail
    cases failed
  · simp only [busy] at tail
    have empty := busy
    simp only [Bool.or_eq_true,not_or,Bool.not_eq_true] at empty
    by_cases handshake : (!d.handshakeQueue.empty) = true
    · simp only [handshake,↓reduceIte] at tail
      cases tail
    · simp only [handshake] at tail
      cases tail
      refine ⟨rfl,d,device,?_,?_,?_,?_⟩
      · apply List.isEmpty_iff.mp
        cases flag : d.sendWorkQueue.isEmpty <;> simp_all
      · apply List.isEmpty_iff.mp
        cases flag : d.clearWorkQueue.isEmpty <;> simp_all
      · cases flag : d.encryptQueue.empty <;> simp_all
      · apply List.isEmpty_iff.mp
        cases flag : d.txWorkQueue.isEmpty <;> simp_all

/-- The guard rules out even an empty batch ghost: the native service account
requires every queued batch to have a resident head and actual service. -/
theorem check_queues (service : TxWork.Serving [] [] [] w)
    (run : (TxWork.Destruct.check.run w).run a = .ok (((),v),b)) :
    txQueueContents w = fun _ => [] := by
  obtain ⟨_,d,device,_,_,crypt,tx⟩ := check_fields run
  obtain ⟨n,h,physical⟩ := service.2.1.2.2.physical d device
  have ring : txCryptItems w = [] := by
    simpa only [txCryptItems,device,Option.map_some,Option.getD_some] using
      TxWork.ring_empty physical crypt
  have work : TxWork.queued w = [] := by simp [TxWork.queued,device,tx]
  have empty := TxWork.no_queues service.1 ring work
  funext pid
  cases found : peerAt w pid with
  | none =>
    change ((peerAt w pid).map (·.txQueue.all)).getD [] = []
    rw [found]
    rfl
  | some p =>
    change ((peerAt w pid).map (·.txQueue.all)).getD [] = []
    rw [found]
    exact empty pid p found

/-- At the actual normal guard cut, the SAME physical holder account has no
remaining occurrence. Its upper half plus positivity therefore proves all
old staged queues empty, including unconfigured retired peers. -/
theorem checked_staged (service : TxWork.Serving [] [] [] w)
    (funded : holders.Funded [] [] w) (upper : RetiredPeer.Upper holders [] [] w)
    (base : (w.dev.map Device.peerList).getD [] = [])
    (cursor7 : DurableHolders.activeCursor w.nlSock7 = none)
    (cursor8 : DurableHolders.activeCursor w.nlSock8 = none)
    (positive : ∀ (d : Device) (pid : PeerId) (p : Peer),
      w.dev = some d → d.peers[pid]? = some p → 0 < p.refcount)
    (run : (TxWork.Destruct.check.run w).run a = .ok (((),v),b)) :
    ∀ epoch pid stamp, stagedPackets epoch pid stamp w = [] := by
  obtain ⟨_,d,device,send,clear,_,_⟩ := check_fields run
  have empty := RetiredPeer.holders_empty funded base
    (by intro other found; have same := Option.some.inj (device.symm.trans found); subst other; exact send)
    (by simp [device,clear]) (check_queues service run) cursor7 cursor8
  exact RetiredPeer.staged_empty upper empty positive

/-- This native suffix preserves one paired ledger after actual guard success.
All missing initialized facts remain named at its incoming native cut. -/
theorem tail_from_account (before : Accounted history ledger [] [] w)
    (service : TxWork.Serving [] [] [] w)
    (funded : holders.Funded [] [] w) (upper : RetiredPeer.Upper holders [] [] w)
    (base : (w.dev.map Device.peerList).getD [] = [])
    (cursor7 : DurableHolders.activeCursor w.nlSock7 = none)
    (cursor8 : DurableHolders.activeCursor w.nlSock8 = none)
    (positive : ∀ (d : Device) (pid : PeerId) (p : Peer),
      w.dev = some d → d.peers[pid]? = some p → 0 < p.refcount)
    (run : (tail.run w).run a = .ok (((),v),b)) :
    Accounted history ledger [] [] v ∧ Retired.NoPending ledger := by
  have sourceRun := run
  simp only [tail,MaterialOrigin.bind_ok_ambient] at sourceRun
  obtain ⟨value,u,c,checked,_⟩ := sourceRun
  cases value
  exact tail_returned before service
    (checked_staged service funded upper base cursor7 cursor8 positive checked) run

/-- Required facts at the literal guard entry, using one explicit holder list.
This is a local source precondition; initialized caller coverage remains work. -/
structure GuardEntry (history : List Event) (ledger : Staged.Obligations.Ledger)
    (holders : DurableHolders) (w : WGWorld) : Prop where
  accounted : Accounted history ledger [] [] w
  service : TxWork.Serving [] [] [] w
  funded : holders.Funded [] [] w
  upper : RetiredPeer.Upper holders [] [] w
  base : (w.dev.map Device.peerList).getD [] = []
  cursor7 : DurableHolders.activeCursor w.nlSock7 = none
  cursor8 : DurableHolders.activeCursor w.nlSock8 = none
  positive : ∀ (d : Device) (pid : PeerId) (p : Peer),
    w.dev = some d → d.peers[pid]? = some p → 0 < p.refcount

/-- The native final suffix preserves the old terminal ledger on return.
At Stop it retains the actual guard-entry account, with no fictitious final
world and no reset-generated receipt or terminal. -/
theorem tail_accounted_checked : StatePrefixEnsures
    (fun h w _ => GuardEntry h ledger holders w)
    (CompleteCarrier.Safe ledger [] []) (liftWGPrefix tail)
    (fun _ h w _ => Accounted h ledger [] [] w ∧ Retired.NoPending ledger) := by
  apply StatePrefixEnsures.lift _ (fun _ w _ before => ⟨w,before.accounted⟩)
  intro h w a value v b before run
  cases value
  exact tail_from_account before.accounted before.service before.funded before.upper
    before.base before.cursor7 before.cursor8 before.positive run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRetired
