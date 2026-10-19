import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAcquireFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpCredits
import Leanux.Proofs.WG.Queues.HandshakeCookiePayment

/-! Handshake acquisition retains the same concrete holder account. Both
reference bounds use the owner extracted from the actual native increment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

theorem Account.loan (account : Account holders cs loans w)
    (loan : Loan w (some pid) v) (keys : KeyEffect NoPromotion w v)
    (frame : Frame w v) (stable : stableView v = stableView w) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Account holders cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  obtain ⟨d,p,device,stored,positive,upper⟩ := account.upper.loan loan
  obtain ⟨other,q,otherDevice,otherStored,_,funded⟩ :=
    loan_protected loan account.funded.carriers.funded
  have eq := Option.some.inj (device.symm.trans otherDevice)
  subst other
  have eq := Option.some.inj (stored.symm.trans otherStored)
  subst q
  have carrier : CarrierState cs (⟨d.ifindex,pid,p.internalId⟩ :: (holders.owners ++ loans)) v :=
    ⟨inventory_view account.funded.carriers.inventory (loan_rx loan),
      queueOwners_base account.funded.carriers.queues (loan_base loan),funded,
      keys.rxCompatible (loan_rx loan) account.funded.carriers.keys.1,
      keys.currentsCompatible account.funded.carriers.keys.2 (fun _ _ h => h.elim)⟩
  exact ⟨d,p,device,stored,positive,
    ⟨account.funded.aligned.frame frame,WorkReservations.carrier_loans_perm carrier List.perm_middle.symm⟩,
    upper,account.stable.view stable⟩

/-- A successful public-key lookup charges exactly its native peer allocation;
there is no independent choice of a lower-account owner. -/
theorem Account.pubkey (account : Account holders cs loans w) (key : Key) (a b : Ambient)
    (run : ((pubkeyLookup key).run w).run a = .ok ((some pid,v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Account holders cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (Leanux.Proofs.WG.AllowedIps.pubkeyLookup_borrowed_spec key (wgStoreView w))
    w a (some pid) v b rfl run
  obtain ⟨d,p,device,stored,positive,effect⟩ := borrowed
  have dev : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
    congrArg WGStoreView.dev effect
  change w.dev = some d at device
  have loan : Loan w (some pid) v :=
    ⟨d,p,device,stored,positive,
      by simp only [peerView,creditWorld,dev,Option.map_some,Option.bind_some],
      by simp only [rxView,dev,device,Option.map_some,Option.bind_some]⟩
  have views := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeLoans.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans.pubkey_views) key)
    w a (some pid) v b run
  have frame := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeLoans.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans.pubkey_frame) key w)
    w a (some pid) v b (Frame.refl w) run
  exact account.loan loan (keyEffect_of_view (congrArg Prod.snd views)) frame (congrArg Prod.fst views)

theorem Account.pubkey_none (account : Account holders cs loans w) (key : Key) (a b : Ambient)
    (run : ((pubkeyLookup key).run w).run a = .ok ((none,v),b)) :
    Account holders cs loans v := by
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (Leanux.Proofs.WG.AllowedIps.pubkeyLookup_borrowed_spec key (wgStoreView w))
    w a none v b rfl run
  exact account.store borrowed

/-- Strict get and nullable lookup use the same explicit occurrence format. -/
theorem Account.acquire (account : Account holders cs loans w) (pid : PeerId) (a b : Ambient)
    (run : ((peerGet pid).run w).run a = .ok (((),v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Account holders cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  have credits : Dump.Credits cs (holders.owners ++ loans) w :=
    ⟨⟨account.funded.carriers,account.stable⟩,by simpa [Upper,owners] using account.upper⟩
  obtain ⟨d,p,device,stored,positive,post⟩ := credits.acquire pid a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderDecrypt.peerGet_frame pid w)
    w a () v b (Frame.refl w) run
  refine ⟨d,p,device,stored,positive,
    ⟨account.funded.aligned.frame frame,WorkReservations.carrier_loans_perm post.lower.1 List.perm_middle.symm⟩,
    ?_,post.lower.2⟩
  apply post.upper.relabel
  simpa [owners] using (List.perm_middle (a := ⟨d.ifindex,pid,p.internalId⟩)
    (l₁ := holders.owners) (l₂ := loans)).symm

theorem Account.native_fields {action : WG.M α} (same : SameView HolderEncrypt.fields action) :
    Preserves (Account holders cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b account run
  exact account.fields ((ProjectedAction.iff_run_ambient _ _ _).mp same w a x v b run)

theorem Account.update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (Account holders cs loans) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b account run
  have lower := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_peer)
      pid f stamp count rx napi current tx)
    w a x v b ⟨account.funded,account.stable⟩ run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,c,getter,write⟩ := run
  obtain ⟨rfl,rfl,d,device,stored⟩ := getPeer_normal pid w read p a c getter
  cases write
  refine ⟨lower.1,account.upper.peer_view ?_,lower.2⟩
  simp only [peerView,device,Option.map_some,Option.bind_some]
  congr 1
  funext q
  by_cases eq : pid=q
  · subst q; simp [stored,stamp,count,rx]
  · simp [Std.TreeMap.getElem?_insert,eq]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
