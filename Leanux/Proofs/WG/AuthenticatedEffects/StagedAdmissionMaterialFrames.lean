import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationDisposalMaterialFrames

/-! Native frames for the epoch and allocated packet material around every
front checkpoint. The projection retains packet identity, plaintext, peer, key
and nonce; it deliberately omits the encrypted bytes and scheduling mark. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Material
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
set_option maxHeartbeats 600000

abbrev view := PacketOrigins.snapshot

theorem store {action : WG.M α} (same : SameWGStore action) : SameView view action :=
  same.of_factor (fun s => view {dev := s.dev}) view (fun _ => rfl)

theorem read_peer (pid : PeerId) : SameView view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  exact congrArg view (Peers.getPeer_current pid w v value a b run).1

theorem lookup (family addr : Nat) : SameView view (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    change (PacketOrigins.epoch v,PacketMaterial.view v) = (PacketOrigins.epoch w,PacketMaterial.view w)
    apply Prod.ext
    · simp only [PacketOrigins.epoch,same]
    · funext id
      simp only [PacketMaterial.view,TxDisposition.txPackets,same]
  | some pid =>
    obtain ⟨d,p,device,_,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} :=
      congrArg WGStoreView.dev after
    change (PacketOrigins.epoch v,PacketMaterial.view v) = (PacketOrigins.epoch w,PacketMaterial.view w)
    apply Prod.ext
    · simp only [PacketOrigins.epoch,device,endpoint,Option.map_some]
    · funext id
      simp only [PacketMaterial.view,TxDisposition.txPackets,device,endpoint,Option.bind_some]

theorem check (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    SameView view (Packets.txCheck family addr packets mtu) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  have errors : Preserves (fun w => view w = initial)
      (modifyDev (fun d => {d with txErrors := d.txErrors+1})) :=
    PacketOrigins.modify (fun d => {d with txErrors := d.txErrors+1}) (fun _ => rfl) (fun _ => rfl) initial
  have ambient {α : Type} (a : AmbientM α) : Preserves (fun w => view w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  routing_tx_source [Packets.txCheck,Packets.txHeaders] using [errors,ambient]
  all_goals exact hoare_liftAmbient _ _

theorem error (family : Nat) (first : Packet) (ret : Int) : SameView view (Packets.txError family first ret) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves (fun w => view w = initial) (loopbackSend sites raised) :=
    store (loopbackSend_kernel sites raised) initial
  have ambient {α : Type} (a : AmbientM α) : Preserves (fun w => view w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  have routing {α : Type} (a : Net.M α) : Preserves (fun w => view w = initial) (monadLift a : WG.M α) :=
    store (liftRouting_sameWGStore a) initial
  have errors : Preserves (fun w => view w = initial)
      (modifyDev (fun d => {d with txErrors := d.txErrors+1})) :=
    PacketOrigins.modify (fun d => {d with txErrors := d.txErrors+1}) (fun _ => rfl) (fun _ => rfl) initial
  rxstack_preserves_source [Packets.txError,branch,skipCutSites] using [loopback,ambient,routing,errors]

theorem walk (packets : List Packet) (mtu : Nat) (acc : List Packet) :
    SameView view (Packets.txWalk packets mtu acc) := store (RxCredits.txWalk_kernel packets mtu acc)

theorem trim (pid : PeerId) : SameView view (xmitTrim pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  exact Prod.ext (HandshakeSecurity.StagedDisposal.overflow_epoch pid ⟨value,w,v,a,b⟩ run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (trim_packet_material pid) w a value v b run)

theorem release (peer : Option PeerId) : SameView view (HandshakeSecurity.StagedDisposal.releaseCut peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  refine Prod.ext ?_ ((ProjectedAction.iff_run_ambient _ _ _).mp (release_packet_material peer) w a value v b run)
  cases value with
  | none => exact (Native.release_none peer ⟨none,w,v,a,b⟩ run rfl).1
  | some pair =>
    rcases pair with ⟨pid,p⟩
    obtain ⟨_,_,_,_,_,_,_,epoch,_⟩ := HandshakeSecurity.StagedDisposal.release_exact peer
      ⟨some (pid,p),w,v,a,b⟩ run pid p rfl
    exact epoch

theorem finish (pid : PeerId) (p : Peer) : SameView view (HandshakeSecurity.StagedDisposal.releaseFinish pid p) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases pending : PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome) with
  | some t =>
    simp [HandshakeSecurity.StagedDisposal.releaseFinish,pending,invariant,AmbientM.invariant] at run
    cases run
  | none =>
    simp [HandshakeSecurity.StagedDisposal.releaseFinish,pending,retirePeerUnits,modifyAmbient] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    rfl

theorem splice (pid : PeerId) (packets : List Packet) : SameView view (xmitSplice pid packets) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases value
  obtain ⟨d,p,device,_,changed,_⟩ := Staged.splice pid packets ⟨(),w,v,a,b⟩ run
  dsimp only at device changed
  change (PacketOrigins.epoch v,PacketMaterial.view v) = (PacketOrigins.epoch w,PacketMaterial.view w)
  apply Prod.ext
  · simp only [PacketOrigins.epoch,device,changed,Option.map_some]
  · funext id
    simp only [PacketMaterial.view,TxDisposition.txPackets,device,changed,Option.bind_some]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Material
