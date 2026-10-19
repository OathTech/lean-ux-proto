import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedSource

/-! Exact native entry frames and the extra peer reference acquired by the
queued-initiation prefix. No incoming global reference-count invariant is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queued
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity Queues.RxCredits
open Std.Do
set_option maxHeartbeats 600000

theorem replace_peer (device : w.dev = some d) (resident : d.peers[pid]? = some p)
    (stamp : q.internalId = p.internalId) (staged : q.staged = p.staged)
    (queued : q.txQueue = p.txQueue) :
    StagedEntry.view {w with dev := some {d with peers := d.peers.insert pid q}} = StagedEntry.view w := by
  unfold StagedEntry.view
  apply Prod.ext
  · simp [Packets.epoch,device]
  apply Prod.ext
  · funext other
    by_cases same : pid = other
    · subst other; simp [Staged.stagedAt,device,resident,stamp,staged]
    · simp [Staged.stagedAt,device,Std.TreeMap.getElem?_insert,same]
  apply Prod.ext
  · funext id
    simp [PacketMaterial.view,TxDisposition.txPackets,device]
  apply Prod.ext
  · simp [Packets.snapshot,Packets.deviceStore,device]
  apply Prod.ext
  · funext id; simp [TxDisposition.txPackets,device]
  · funext other
    by_cases same : pid = other
    · subst other; simp [txQueueContents,handoffTxView,device,resident,queued]
    · simp [txQueueContents,handoffTxView,device,Std.TreeMap.getElem?_insert,same]

theorem update (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue) :
    SameView StagedEntry.view (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,write⟩ := run
  have sameWorld : u = w := (Peers.getPeer_current pid w u p a c read).1
  subst u
  cases device : w.dev with
  | none =>
    simp [getPeer,getDev,device,invariant,AmbientM.invariant] at read
    cases read
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at read
      cases read
    | some stored =>
      simp [getPeer,getDev,device,resident] at read
      obtain ⟨rfl,rfl⟩ := read
      simp [setPeer,modifyDev,device] at write
      rcases write with ⟨⟨rfl,rfl⟩,rfl⟩
      exact replace_peer device resident (same stored).1 (same stored).2.1 (same stored).2.2

theorem update_bind (initial : _) (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue)
    (tail : ∀ value, Preserves (fun w => StagedEntry.view w = initial) (next value)) :
    Preserves (fun w => StagedEntry.view w = initial) (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind ((update pid f same).wp (· = initial)) tail

theorem acquire (pid : PeerId) : SameView StagedEntry.view (peerGet pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.strict_acquire_spec pid (wgStoreView w)) w a value v b rfl run
  obtain ⟨d,p,device,resident,_,after⟩ := borrowed
  change w.dev = some d at device
  have endpoint := congrArg WGStoreView.dev after
  change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} at endpoint
  have result := replace_peer device resident (q := {p with refcount := p.refcount+1}) rfl rfl rfl
  change StagedEntry.view {dev := v.dev} = _
  rw [endpoint]
  exact result

theorem read (pid : PeerId) : SameView StagedEntry.view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg StagedEntry.view (Peers.getPeer_current pid w v p a b run).1

macro "queued_entry_step " initial:term : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply update_bind $initial
     · intro p; exact ⟨rfl,rfl,rfl⟩
     intro ignored)
  | (receive_update_head setPeer; apply (update _ _ (fun _ => ⟨rfl,rfl,rfl⟩)).wp (· = $initial))
  | (rx_retention_head getPeer; exact (read _).wp (· = $initial))
  | (rx_retention_head peerGet; exact (acquire _).wp (· = $initial))
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => StagedEntry.view w = $initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

theorem decision_views (pid : PeerId) : SameView StagedEntry.view (decisionPrefix pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold decisionPrefix readyPrefix borrowedDecision
  simp only [branch,peekQueuedUnit]
  repeat' queued_entry_step initial

theorem install_views (pid : PeerId) : SameView StagedEntry.view (install pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold install
  simp only [recordQueued]
  repeat' queued_entry_step initial

def Funded (pid : PeerId) (w : WGWorld) : Prop :=
  ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) = some n

/-- The successful strict borrow supplies the extra resident reference. -/
theorem acquired (pid : PeerId) (a b : Ambient)
    (run : ((peerGet pid).run w).run a = .ok (((),v),b)) : Funded pid v := by
  exact ((hoare_iff_run_ambient _ _ _).mp
    (AllocatedObligation.Publication.acquire_staged pid (Staged.stagedAt w)) w a () v b rfl run).2

/-- The actual successful decision prefix carries its own paired borrow.
Early refusal returns none and creates no repayment obligation. -/
theorem decision_funded (pid : PeerId) (a b : Ambient)
    (run : ((decisionPrefix pid).run w).run a = .ok ((some decision,v),b)) : Funded pid v := by
  unfold decisionPrefix at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,_,tail⟩ := run
  cases ready with
  | none => cases tail
  | some p =>
    unfold borrowedDecision at tail
    simp only [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,t,e,borrow,peek,s,f,peekRun,queued,z,g,branchRun,last⟩ := tail
    cases ignored
    have peekSame : s = t := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.peekQueuedUnit .sendWorker pid) (fun state => state = t))
      t e peek s f rfl peekRun
    subst s
    have branchSame : z = t := by cases branchRun; rfl
    subst z
    cases last
    exact acquired pid c e borrow

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queued
