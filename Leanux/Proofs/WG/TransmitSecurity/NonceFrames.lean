import Leanux.Proofs.WG.TransmitSecurity.NonceSource
import Leanux.Proofs.WG.RetirementSecurity.Acquire
import Leanux.Proofs.WG.Queues.WorkQueueFrames

/-! Frames for the sending-counter projection. Peer, index and queue bookkeeping
cannot reset a retained key's nonce frontier. Key retirement may remove it. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

namespace Frames

theorem update (f : Device → Device) (keys : ∀ d, (f d).keypairs = d.keypairs) :
    SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b hr
  cases hr
  apply View.ext
  · rfl
  · funext id
    simp [view, Option.bind_map, Function.comp_def, keys]

theorem peer_read (pid : PeerId) : SameView view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b hr
  exact congrArg view (Peers.getPeer_current pid w v p a b hr).1

theorem key_read (kid : KeypairId) : SameView view (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b hr
  exact congrArg view (Keypairs.getKeypair_current kid w v a b k hr).1

theorem peer_write (pid : PeerId) (p : Peer) : SameView view (setPeer pid p) :=
  update _ (fun _ => rfl)

theorem index {α : Type} (a : IndexM α) : SameView view (liftIndex a) := by
  intro initial
  apply hoare_liftIndex
  intro w d table hi hd
  rw [← hi]
  apply View.ext
  · rfl
  · funext id
    simp [view,hd]

macro "nonce_frame_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact (peer_read _).wp (fun s => s = $initial))
  | (rx_retention_head getKeypair; exact (key_read _).wp (fun s => s = $initial))
  | (rx_retention_head setPeer; exact (peer_write _ _).wp (fun s => s = $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head modifyDev
     apply (update _ ?_).wp (fun s => s = $initial)
     intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact (index _).wp (fun s => s = $initial))
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | rx_retention_step)

theorem peerGet (pid : PeerId) : SameView view (WG.peerGet pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold WG.peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' nonce_frame_step initial

theorem peerPut (pid : Option PeerId) : SameView view (WG.peerPut pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold WG.peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' nonce_frame_step initial

theorem queuedHandshake (pid : PeerId) (retry : Bool) :
    SameView view (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head WG.peerGet; exact (peerGet _).wp (fun s => s = initial))
    | (rx_retention_head WG.peerPut; exact (peerPut _).wp (fun s => s = initial))
    | (rx_retention_head branchExpired; exact ((branchExpired_sameWGWorld _ _ _ _).factor view).wp (fun s => s = initial))
    | nonce_frame_step initial

theorem key_put (kp : Option KeypairId) (now : Bool) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (keypairPut kp now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result
  have he := RetirementSecurity.put_nonce_projection kp now w v a b hr
  apply hi.subset (t := view v) (by exact Nat.le_of_eq he.1.symm)
  intro id c hc
  simp only [view] at hc ⊢
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨old, ho, stamp, counter⟩ := he.2 id k hk
  rw [show (w.dev.bind fun d => d.keypairs[id]?) = some old from ho]
  simp only [Option.map_some, Option.some.injEq]
  exact Cell.ext stamp.symm counter.symm

theorem key_get (kp : Option KeypairId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (keypairGet kp) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have he := RetirementSecurity.get_nonce_projection kp w v a b result hr
  apply hi.subset (t := view v) (by exact Nat.le_of_eq he.1.symm)
  intro id c hc
  simp only [view] at hc ⊢
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨old, ho, stamp, counter⟩ := he.2 id k hk
  rw [show (w.dev.bind fun d => d.keypairs[id]?) = some old from ho]
  simp only [Option.map_some, Option.some.injEq]
  exact Cell.ext stamp.symm counter.symm

theorem update_key (slot : KeypairId) (f : Keypair → Keypair) (hc : ∀ k, cell (f k) = cell k) :
    SameView view (do let k ← getKeypair slot; setKeypair slot (f k)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases hd : w.dev with
  | none =>
    simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[slot]? with
    | none =>
      simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some k =>
      simp only [StateT.run_bind, CounterWindow.getKeypair_run w a d slot k hd hk,
        CounterWindow.except_ok_bind, CounterWindow.setKeypair_run] at hr
      cases hr
      rw [view_store w d slot (f k) hd, hc k]
      apply View.ext
      · rfl
      · funext id
        by_cases same : id = slot
        · subst id
          simp [View.put, view_lookup w d slot k hd hk]
        · simp [View.put, same]

theorem native_frame {α : Type} {a : WG.M α} (h : List Allocation)
    (frame : SameView view a) : Preserves (fun w => Inv (view w) h) a :=
  frame.wp (fun v => Inv v h)

theorem ambient {α : Type} (a : AmbientM α) : SameView view (monadLift a : WG.M α) :=
  fun initial => hoare_liftAmbient a (fun w => view w = initial)

theorem device_read : SameView view getDev := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a d v b hr
  cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
  · cases hr
  · obtain ⟨⟨rfl,rfl⟩,rfl⟩ := hr
    rfl

/-- The skb adapter's type separates packet bookkeeping from key state. -/
theorem skb {α : Type} (a : SkbM α) : SameView view (liftSkb a) := by
  intro initial
  apply hoare_liftSkb
  intro w d skbs hi hd
  rw [← hi]
  apply View.ext
  · rfl
  · funext id
    simp [view,hd]

theorem packet_read (id : SkbId) : SameView view (getTxSkb id) := skb _
theorem packet_write (id : SkbId) (f : DataPacket → DataPacket) :
    SameView view (setTxSkb id f) := skb _
theorem packet_free (id : SkbId) : SameView view (freeTxSkb id) := skb _
theorem packet_new (pkt : DataPacket) : SameView view (newTxSkb pkt) := skb _

/-- Lifting a native frame retains the journal even when native execution stops. -/
theorem lift_frame {α : Type} {a : WG.M α} (frame : SameView view a) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.nodup)
  intro h w ambient x v ambient' hi hr
  have he := (ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient x v ambient' hr
  simpa [he] using hi

theorem lift_preserves {α : Type} {a : WG.M α}
    (frame : ∀ h, Preserves (fun w => Inv (view w) h) a) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.nodup)
  intro h w ambient x v ambient' hi hr
  exact (hoare_iff_run_ambient _ _ _).mp (frame h) w ambient x v ambient' hi hr

end Frames
end Leanux.Proofs.WG.TransmitSecurity.Nonce
