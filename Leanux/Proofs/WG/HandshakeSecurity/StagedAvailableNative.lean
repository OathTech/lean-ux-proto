import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityFrames
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedCreationFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedTrim
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrontFrames

/-! Native frames for still-available staged birth credits. Overflow removes a
prefix; these calls do not append allocation events or revive spent credits. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Std.Do
set_option maxHeartbeats 600000

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Inv h) action :=
  frame (same.of_factor (fun s => s.dev.map Device.ifindex) Packets.epoch (fun _ => rfl))
    (Staged.store _ same)

theorem read_peer (pid : PeerId) : Preserves (Inv h) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  exact (getPeer_normal pid w v p a b run).1 ▸ before

theorem read_key (kid : KeypairId) : Preserves (Inv h) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b before run
  exact (KeyTimes.getKeypair_return kid w v key a b run).1 ▸ before

theorem modify_device (f : Device → Device)
    (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (peers : ∀ d, (f d).peers = d.peers) : Preserves (Inv h) (modifyDev f) := by
  apply frame
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    cases run
    simp [Packets.epoch,Option.map_map,Function.comp_def,epoch]
  · exact Staged.modify_device f peers

theorem peer_put (pid : Option PeerId) : Preserves (Inv h) (peerPut pid) :=
  frame (PacketOrigins.epoch_ring (TxRing.peerPut_frame pid)) (Staged.peer_put pid)

theorem key_get (kid : Option KeypairId) : Preserves (Inv h) (keypairGet kid) :=
  frame (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire kid).factor Prod.fst))
    (Staged.key_get kid)

theorem lookup (family addr : Nat) : Preserves (Inv h) (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    apply before.retains
    · simp [Packets.epoch,same]
    · intro pid cell found
      simpa only [stagedAt,same] using found
  | some pid =>
    obtain ⟨d,p,device,resident,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} :=
      congrArg WGStoreView.dev after
    apply before.retains
    · simp [Packets.epoch,endpoint,device]
    · intro q cell found
      by_cases same : pid = q
      · subst q; simpa [stagedAt,endpoint,device,resident] using found
      · simpa [stagedAt,endpoint,device,Std.TreeMap.getElem?_insert,same] using found

theorem trim_epoch (pid : PeerId) : SameView Packets.epoch (xmitTrim pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.xmitTrim_view) pid).of_factor
    (fun state => state.map ConfiguredIdentity.State.epoch) Packets.epoch
    (fun w => by simp only [ConfiguredIdentity.view,ConfiguredIdentity.state,Packets.epoch,
      Option.map_map,Function.comp_def])

theorem partition (pid : PeerId) (before : Inv h w)
    (p : HandshakeSecurity.StagedDisposal.Partition pid w v) : Inv h v := by
  intro generation epoch q stamp packets resident
  by_cases same : q = pid
  · subst q
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (p.after.symm.trans resident))
    exact (before generation (p.epoch ▸ epoch) pid p.stamp p.packets p.before).drop p.removed
  · exact before generation (p.epoch ▸ epoch) q stamp packets
      ((p.others q (Ne.symm same)) ▸ resident)

theorem trim (pid : PeerId) : Preserves (Inv h) (xmitTrim pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨p⟩ := HandshakeSecurity.StagedDisposal.overflow_exact pid ⟨result,w,v,a,b⟩ run
  exact partition pid before p

theorem purge (pid : PeerId) : Preserves (Inv h) (purgeStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨p,_⟩ := HandshakeSecurity.StagedDisposal.purge_exact pid ⟨result,w,v,a,b⟩ run
  exact partition pid before p

theorem key_put (kid : Option KeypairId) (now : Bool) :
    Preserves (Inv h) (keypairPut kid now) :=
  frame (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid now)) (Staged.key_put kid now)

theorem peer_get (pid : PeerId) : Preserves (Inv h) (peerGet pid) :=
  frame (PacketOrigins.epoch_ring (TxRing.peerGet_frame pid)) (Staged.acquire_peer pid)

theorem write_key (kid : KeypairId) (key : Keypair) : Preserves (Inv h) (setKeypair kid key) :=
  modify_device _ (fun _ => rfl) (fun _ => rfl)

theorem create (pid : PeerId) (items : List SkbId) : Preserves (Inv h) (createData pid items) :=
  frame (Origins.create_epoch pid items) (Staged.create pid items)

theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    Preserves (Inv h) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply frame
  · apply SameView.bind
    · exact PacketOrigins.epoch_ring (TxRing.getPeer_frame pid)
    · intro p
      exact PacketOrigins.epoch_ring (TxRing.setPeer_frame pid (f p))
  · exact Staged.update_peer pid f same

theorem update_peer_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged)
    (tail : ∀ x, Preserves (Inv h) (next x)) :
    Preserves (Inv h) (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind (update_peer pid f same) tail

theorem queued (pid : PeerId) (retry : Bool) :
    Preserves (Inv h) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (receive_update_head Bind.bind
       apply update_peer_bind
       · intro p; exact ⟨rfl,rfl⟩
       intro x)
    | (receive_update_head setPeer; apply update_peer; intro p; exact ⟨rfl,rfl⟩)
    | (rx_retention_head getPeer; exact read_peer _)
    | (rx_retention_head peerGet; exact peer_get _)
    | (rx_retention_head peerPut; exact peer_put _)
    | (rx_retention_head modifyDev; apply modify_device <;> intro d <;> rfl)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Inv h))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem check (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Preserves (Inv h) (Packets.txCheck family addr packets mtu) := by
  have errors := modify_device (h := h) (fun d => {d with txErrors := d.txErrors+1})
    (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (Inv h)
  routing_tx_source [Packets.txCheck,Packets.txHeaders] using [errors,ambient]
  all_goals exact hoare_liftAmbient _ _

theorem select (family : Nat) (packets : List Packet) (mtu : Nat) (peer : Option PeerId) :
    Preserves (Inv h) (Packets.txSelect family packets mtu peer) := by
  have getter := read_peer (h := h)
  have pay := peer_put (h := h)
  have trimming := trim (h := h)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves (Inv h) (loopbackSend sites raised) :=
    store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (Inv h)
  have routing {α : Type} (a : Net.M α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    store (liftRouting_sameWGStore a)
  have errors := modify_device (h := h) (fun d => {d with txErrors := d.txErrors+1})
    (fun _ => rfl) (fun _ => rfl)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (safe : ∀ x b, Preserves (Inv h) (f x b)) : Preserves (Inv h) (forIn xs init f) :=
    list_view_spec id (Inv h) xs init f safe
  rxstack_preserves_source [Packets.txSelect,Packets.txError,Packets.txWalk,WG.andM,
      branch,invariant,skipCutSites,envOk]
    using [getter,pay,trimming,loopback,ambient,routing,errors,loop]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
