import Leanux.Proofs.WG.Queues.RxReservationPayment

/-! Clear-work execution consumes its explicit queued-work reservation.
The normal-endpoint contracts retain the original carrier ledger and do not
infer a reservation from an unverified pending flag or spare reference count. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ClearWork
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

abbrev Inv (cs : Ledger) (loans : Reservations) (w : WGWorld) :=
  CarrierState cs loans w ∧ StableRx cs w

private theorem peer_update (hi : Inv cs loans w) (hd : w.dev = some d)
    (hp : d.peers[pid]? = some old) (p : Peer)
    (stamp : p.internalId = old.internalId) (count : p.refcount = old.refcount)
    (queue : p.rxQueue = old.rxQueue) (napi : p.napiScheduled = old.napiScheduled)
    (current : ∀ kid, p.keypairCurrent = some kid → old.keypairCurrent = some kid) :
    Inv cs loans {w with dev := some {d with peers := d.peers.insert pid p}} := by
  let out : WGWorld := {w with dev := some {d with peers := d.peers.insert pid p}}
  have peers : peerView out = peerView w := by
    simp only [peerView,out,hd,Option.map_some,Option.bind_some]
    refine Prod.ext rfl ?_
    funext q
    by_cases chosen : pid = q <;>
      simp_all [Std.TreeMap.getElem?_insert]
  have packets : rxView out = rxView w := by simp [rxView,out,hd]
  have rxkeys : RxCompatible out := by
    intro after id pkt ha hx other key ho hk
    have eq : after = {d with peers := d.peers.insert pid p} := Option.some.inj ha.symm
    have eq' : other = after := Option.some.inj (ho.symm.trans ha)
    subst other; subst after
    exact hi.1.keys.1 d id pkt hd hx d key hd hk
  have currents : CurrentsCompatible out := by
    intro q after peer kid ha hq hc other key ho hk
    have eq : after = {d with peers := d.peers.insert pid p} := Option.some.inj ha.symm
    have eq' : other = after := Option.some.inj (ho.symm.trans ha)
    subst other; subst after
    by_cases chosen : pid = q
    · subst q
      have same : peer = p := by simpa using hq.symm
      subst peer
      exact hi.1.keys.2 pid d old kid hd hp (current kid hc) d key hd hk
    · exact hi.1.keys.2 q d peer kid hd
        (by simpa [Std.TreeMap.getElem?_insert,chosen] using hq) hc d key hd hk
  refine ⟨⟨inventory_view hi.1.inventory packets,queueOwners_view hi.1.queues peers,
    protected_view hi.1.funded peers,rxkeys,currents⟩,?_⟩
  apply hi.2.view
  simp only [stableView,hd,RxRing.nativeCell,rxView,Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext q
  by_cases chosen : pid = q <;> simp_all [Std.TreeMap.getElem?_insert]

private theorem modify_peer (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (count : ∀ p, (f p).refcount = p.refcount)
    (queue : ∀ p, (f p).rxQueue = p.rxQueue)
    (napi : ∀ p, (f p).napiScheduled = p.napiScheduled)
    (current : ∀ p kid, (f p).keypairCurrent = some kid → p.keypairCurrent = some kid) :
    Preserves (Inv cs loans) (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,read,middle,hread,hwrite⟩ := hr
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w read p a middle hread
  cases hwrite
  simpa only [setPeer,modifyDev,hd,Option.map_some] using
    peer_update hi hd hp (f p) (stamp p) (count p) (queue p) (napi p) (current p)

private theorem read_peer (pid : PeerId) : Preserves (Inv cs loans) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  exact (getPeer_normal pid w v p a b hr).1 ▸ hi

private theorem key_put (kid : Option KeypairId) (now : Bool) :
    Preserves (Inv cs loans) (keypairPut kid now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result
  exact ⟨keyPut_state kid now hi.1 a b hr,
    hi.2.view ((ProjectedAction.iff_run_ambient _ _ _).mp (stable_keypairPut kid now) w a () v b hr)⟩

/-- Clearing any possibly aliased peer key slots preserves receive funding,
queue ownership and the stable ring boundary. No key-frontier premise is needed. -/
theorem keypairsClear_preserves (pid : PeerId) : Preserves (Inv cs loans) (keypairsClear pid) := by
  unfold keypairsClear
  apply preserves_bind (read_peer pid)
  intro p
  apply preserves_bind (modify_peer pid (fun p => {p with keypairNext := none})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h))
  intro _
  apply preserves_bind (key_put p.keypairNext true)
  intro _
  apply preserves_bind (read_peer pid)
  intro p
  apply preserves_bind (modify_peer pid (fun p => {p with keypairPrevious := none})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h))
  intro _
  apply preserves_bind (key_put p.keypairPrevious true)
  intro _
  apply preserves_bind (read_peer pid)
  intro p
  apply preserves_bind (modify_peer pid (fun p => {p with keypairCurrent := none})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by intro _ _ h; cases h))
  intro _
  exact key_put p.keypairCurrent true

/-- Index unhashing and zeroing the handshake change no funded RX obligation. -/
theorem handshakeClear_preserves (pid : PeerId) : Preserves (Inv cs loans) (handshakeClear pid) := by
  unfold handshakeClear
  apply preserves_bind (indexOwner_peerDeref_preserves (.handshake pid) (Inv cs loans))
  intro _
  have index : Preserves (Inv cs loans) (liftIndex (indexRemove (.handshake pid))) := by
    apply hoare_liftIndex
    intro g d table hi hd
    refine ⟨hi.1.view ?_,hi.2.view ?_⟩
    · unfold carrierView keyView
      unfold peerView rxView RxCredits.keyWords RxCredits.currentCells
      rw [hd]
      rfl
    · simp [stableView,RxRing.nativeCell,rxView,hd]
  apply preserves_bind index
  intro _
  unfold handshakeZero
  exact modify_peer pid _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h => h)

/-- The queued clear worker pays the supplied source-owned reference exactly
once. Its input must account for that reservation before execution. -/
theorem queued_normal (o : Owner) (hi : Inv cs (o :: loans) w)
    (a b : Ambient)
    (hr : ((queuedExpiredZeroKeyMaterial o.slot).run w).run a = .ok (((),v),b)) :
    Inv cs loans v := by
  unfold queuedExpiredZeroKeyMaterial at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,cleared,ac,hclear,u',keys,ak,hkeys,hpay⟩ := hr
  cases u; cases u'
  have hc := (hoare_iff_run_ambient _ _ _).mp (handshakeClear_preserves o.slot)
    w a () cleared ac hi hclear
  have hk := (hoare_iff_run_ambient _ _ _).mp (keypairsClear_preserves o.slot)
    cleared ac () keys ak hc hkeys
  exact reservation_payment_stable hk.1 hk.2 ak b hpay

end Leanux.Proofs.WG.Queues.RxCredits.ClearWork
