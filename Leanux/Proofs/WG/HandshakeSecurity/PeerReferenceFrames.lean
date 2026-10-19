import Leanux.Proofs.WG.HandshakeSecurity.PeerReference

/-! Native reference-count frames. The release frame accounts for both
nonfinal decrement and final erasure, without assuming a spare loan. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves Inv action :=
  (same.factor (fun s => fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.refcount)).wp Positive

theorem frame {action : WG.M α} (same : SameView view action) : Preserves Inv action :=
  same.wp Positive

theorem read_peer (pid : PeerId) : Preserves Inv (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a peer v b before run
  exact (getPeer_normal pid w v peer a b run).1 ▸ before

theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (positive : ∀ p, 0 < p.refcount → 0 < (f p).refcount) :
    Preserves Inv (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,getter,setter⟩ := run
  obtain ⟨rfl,rfl,d,device,found⟩ := getPeer_normal pid w u peer a c getter
  cases setter
  exact replace before pid (f peer) (positive peer (resident before device found))

theorem update_peer_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (positive : ∀ p, 0 < p.refcount → 0 < (f p).refcount)
    (tail : ∀ x, Preserves Inv (next x)) :
    Preserves Inv (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind (update_peer pid f positive) tail

theorem modify_device (f : Device → Device) (same : ∀ d, (f d).peers = d.peers) :
    Preserves Inv (modifyDev f) := by
  apply frame
  intro initial
  apply hoare_modify
  intro w before
  rw [←before]
  funext pid
  simp [view,Option.bind_map,Function.comp_def,same]

theorem modify_world (f : WGWorld → WGWorld) (same : ∀ w, view (f w) = view w) :
    Preserves Inv (modify f : WG.M Unit) := by
  apply frame
  intro initial
  apply hoare_modify
  intro w before
  simpa only [same] using before

theorem read_key (kid : KeypairId) : Preserves Inv (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b before run
  exact (KeyTimes.getKeypair_return kid w v key a b run).1 ▸ before

theorem write_key (kid : KeypairId) (key : Keypair) : Preserves Inv (setKeypair kid key) :=
  modify_device _ (fun _ => rfl)

theorem index (action : IndexM α) : Preserves Inv (liftIndex action) := by
  apply hoare_liftIndex
  intro w d table before device
  simpa only [Inv,Positive,view,device,Option.bind_some] using before

theorem skb (action : SkbM α) : Preserves Inv (liftSkb action) := by
  apply hoare_liftSkb
  intro w d packets before device
  simpa only [Inv,Positive,view,device,Option.bind_some] using before

theorem peer_put (peer : Option PeerId) : Preserves Inv (peerPut peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  cases peer with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact before
  | some pid =>
    cases device : w.dev with
    | none =>
      simp [peerPut,branch,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases found : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,requireNotPending,getPeer,getDev,device,found,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        obtain ⟨positive,same,_⟩ := RxCredits.peerPut_effect pid w v d p a b device found run
        have counts : view v = view (RxCredits.paymentState w d pid p) := by
          funext other
          simpa [view,RxCredits.peerView,Option.map_map,Function.comp_def] using
            congrArg (fun cells => (cells.2 other).map (fun x => x.2.1)) same
        unfold Inv
        rw [counts]
        by_cases final : p.refcount = 1
        · simpa [Inv,RxCredits.paymentState,final] using erase before device pid
        · have kept := replace before pid {p with refcount := p.refcount - 1}
            (by change 0 < p.refcount - 1; omega)
          simpa [Inv,RxCredits.paymentState,device,final] using kept

theorem maybe_peer (peer : Option PeerId) : Preserves Inv (peerGetMaybeZero peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases peer with
  | none =>
    simp [peerGetMaybeZero,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact before
  | some pid =>
    cases device : w.dev with
    | none =>
      simp [peerGetMaybeZero,branch,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases found : d.peers[pid]? with
      | none =>
        simp [peerGetMaybeZero,branch,requireNotPending,getPeer,getDev,device,found,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        have positive := resident before device found
        have nonzero : p.refcount ≠ 0 := by omega
        by_cases overflow : 2147483647 ≤ p.refcount <;>
          simp [peerGetMaybeZero,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountIncNotZero,branch,branchCmp,AmbientM.branch,AmbientM.branchCmp,
            device,found,nonzero,overflow,unsupported,AmbientM.unsupported] at run
        all_goals try solve | cases run
        all_goals
          obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
          simpa [device] using replace before pid {p with refcount := p.refcount + 1} (by simp)

theorem world {action : WG.M α} (same : SameView id action) : Preserves Inv action :=
  same.wp Inv

theorem read_saved (pid : PeerId) :
    Hoare (getPeer pid) Inv (fun p w => Inv w ∧ 0 < p.refcount) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  obtain ⟨rfl,rfl,d,device,found⟩ := getPeer_normal pid w v p a b run
  exact ⟨before,resident before device found⟩

theorem write_positive (pid : PeerId) (p : Peer) (positive : 0 < p.refcount) :
    Preserves Inv (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases run
  exact replace before pid p positive

theorem write_cell (pid : PeerId) (p q : Peer) (same : q.refcount = p.refcount) :
    Hoare (setPeer pid q) (fun w => Inv w ∧ 0 < p.refcount) (fun _ => Inv) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (hoare_iff_run_ambient _ _ _).mp (write_positive pid q (same ▸ before.2))
    w a result v b before.1 run

theorem write_saved (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, (f p).refcount = p.refcount) :
    Hoare (setPeer pid (f p)) (fun w => Inv w ∧ 0 < p.refcount) (fun _ => Inv) :=
  write_cell pid p (f p) (same p)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
