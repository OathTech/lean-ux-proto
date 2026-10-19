import Leanux.Proofs.WG.TransmitSecurity.StagedOriginFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedTrim
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrontFrames

/-! Native frames for staged origins. Overflow consumes a prefix; ordinary
updates preserve surviving staged lists. These are not conservation claims. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
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

theorem trim (pid : PeerId) : Preserves (Inv h) (xmitTrim pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  have start := run
  unfold xmitTrim at start
  rw [MaterialOrigin.bind_ok_ambient] at start
  obtain ⟨p,u,c,read,_⟩ := start
  obtain ⟨sameWorld,sameAmbient,d,device,resident⟩ := Leanux.Proofs.WG.Origins.getPeer_return pid w u p a c read
  subst u
  subst c
  obtain ⟨n,_,slot,_,others,_⟩ := trim_exact pid ⟨(),w,v,a,b⟩ run d p device resident
  have sameEpoch := (ProjectedAction.iff_run_ambient _ _ _).mp (trim_epoch pid) w a () v b run
  have epoch : Packets.epoch v = some d.ifindex := by rw [sameEpoch]; simp [Packets.epoch,device]
  have batch := (before d.ifindex (by simp [Packets.epoch,device]) pid p.internalId p.staged
    (by simp [stagedAt,device,resident])).drop n
  simpa only [List.append_nil] using before.changed [] sameEpoch epoch slot
    (fun q different => others q (Ne.symm different)) (by simpa only [List.append_nil] using batch)

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

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
