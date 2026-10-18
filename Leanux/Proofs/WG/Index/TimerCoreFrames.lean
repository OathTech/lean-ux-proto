import Leanux.Proofs.WG.Index.TimerCoreModel
import Leanux.Proofs.WG.Index.ClearFrames
import Leanux.Proofs.WG.Index.ResponseIndexFrames
import Leanux.Proofs.WG.Index.LookupCoreSource
import Leanux.Proofs.WG.Index.TimerFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceCallbackFrames
import Leanux.Proofs.WG.Queues.SlotTimers

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TimerCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem ready_of_core {α : Type} (action : WG.M α)
    (slots : Preserves CurrentSlots.Inv action)
    (core : Ensures action Reached.Core (fun _ => Reached.Core)) :
    Ensures action Ready (fun _ => Ready) := by
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp slots w a result v b pre.1 run,
    core w a result v b pre.2 run⟩

theorem acquire (pid : PeerId) :
    Ensures (peerGet pid) Ready (fun _ => Held pid) := by
  intro w a result v b pre run
  have slots := (hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.fields_preserves (project := id) (CurrentSlots.peerGet_fields pid))
      w a result v b pre.1 run
  cases device : w.dev with
  | none => simp [peerGet,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [peerGet,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p =>
      obtain ⟨present,positive⟩ := (ensures_iff _ _ _).mpr
        (Config.peerGet_exact pid d p resident) w a result v b device run
      have core := deviceIndexCore_acquire d pid p resident (pre.2 d device)
      refine ⟨⟨slots,?_⟩,acquirePeer d pid p,{p with refcount:=p.refcount+1},present,by simp [acquirePeer],by change 1 < p.refcount + 1; omega⟩
      intro e ending
      rw [present] at ending
      cases ending
      exact core

theorem repay (pid : PeerId) :
    Ensures (peerPut (some pid)) (Held pid) (fun _ => Ready) := by
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (CurrentSlots.peerPut_preserves (some pid))
    w a result v b pre.1.1 run,peerPut_indexCore_held pid w a result v b ⟨pre.1.2,pre.2⟩ run⟩

theorem sender_core {α : Type} (action : WG.M α)
    (tables : Preserves TablesSafeWG action) (frame : SameView senderFields action) :
    Ensures action Reached.Core (fun _ => Reached.Core) := by
  intro w a result v b pre run
  have table := (hoare_iff_run_ambient _ _ _).mp tables w a result v b (fun d hd => (pre d hd).1) run
  have others := responseIndex_sender_frame action frame w a result v b
    (fun d hd => (pre d hd).2) run
  exact fun d hd => ⟨table d hd,others d hd⟩

theorem del (pid : PeerId) (timer : PeerTimer) :
    Ensures (delTimer pid timer) Ready (fun _ => Ready) :=
  ready_of_core _ (CurrentSlots.delTimer_preserves pid timer)
    (sender_core _ (delTimer_tables pid timer) (sender_delTimer pid timer))

theorem arm (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Ensures (modPeerTimer site pid timer delay) Ready (fun _ => Ready) :=
  ready_of_core _ (CurrentSlots.modPeerTimer_preserves site pid timer delay)
    (sender_core _ (modPeerTimer_tables site pid timer delay) (sender_modPeerTimer site pid timer delay))

theorem modify_slots (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p) :
    Preserves CurrentSlots.Inv (modifyPeer pid f) := by
  apply CurrentSlots.view_preserves (project := id)
  intro initial
  apply (ensures_iff _ _ _).mp
  exact ensures_bind _ _
    ((ensures_iff _ _ _).mpr (Affiliation.getPeer_spec (fun s => s=initial) pid))
    (fun p => (ensures_iff _ _ _).mpr (by
      simpa only [same p,id_eq] using Affiliation.setPeer_spec (fun s => s=initial) pid (f p)))

theorem update (pid : PeerId) (f : Peer → Peer)
    (sender : ∀ p, senderPeerCell (f p)=senderPeerCell p)
    (slots : ∀ p, Affiliation.peerCell (f p)=Affiliation.peerCell p) :
    Ensures (modifyPeer pid f) Ready (fun _ => Ready) :=
  ready_of_core _ (modify_slots pid f slots)
    (sender_core _ (modifyPeer_tables pid f) (sender_modifyPeer pid f sender))

theorem endpoint_frame (pid : PeerId) : SameView senderFields (clearPeerEndpointSrc pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases device : w.dev with
  | none => simp [clearPeerEndpointSrc,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [clearPeerEndpointSrc,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p =>
      obtain ⟨next,reset,present,shape,selected,others⟩ :=
        Config.clearEndpointSource_exact pid d p resident w a result v b device run
      simp only [senderFields,present,device,Option.map_some,Option.some.injEq]
      simp only [senderDeviceCell,Prod.mk.injEq]
      refine ⟨by simpa only using congrArg Device.indexTable shape,
        by simpa only using congrArg Device.ifindex shape,?_,?_⟩
      · funext kid
        exact congrArg (fun d => d.keypairs[kid]?) shape
      · funext target
        by_cases same : target=pid
        · subst target
          simp only [selected,resident,Option.map_some]
          rfl
        · rw [others target same]

theorem endpoint (pid : PeerId) :
    Ensures (clearPeerEndpointSrc pid) Ready (fun _ => Ready) :=
  ready_of_core _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotTimers.«0».Leanux.Proofs.WG.CurrentSlots.Timer.endpoint) pid)
    (sender_core _ (clearPeerEndpointSrc_tables pid) (endpoint_frame pid))

theorem purge_frame (pid : PeerId) : SameView senderFields (purgeStagedPackets pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases device : w.dev with
  | none => simp [purgeStagedPackets,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [purgeStagedPackets,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p =>
      simp [purgeStagedPackets,getPeer,getDev,device,resident,setPeer,modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      simpa only [senderFields,device,Option.map_some,senderDeviceCell] using congrArg some (senderFields_peerWrite
        {d with txDropped:=d.txDropped+p.staged.length} pid p {p with staged:=[]}
        resident rfl)

theorem purge (pid : PeerId) :
    Ensures (purgeStagedPackets pid) Ready (fun _ => Ready) :=
  ready_of_core _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotTimers.«0».Leanux.Proofs.WG.CurrentSlots.Timer.purge) pid)
    (sender_core _ (purgeStagedPackets_tables pid) (purge_frame pid))

theorem enqueue (pid : PeerId) :
    Ensures (modifyDev fun d => {d with clearWorkQueue:=d.clearWorkQueue++[pid]})
      (Held pid) (fun _ => Ready) := by
  intro w a result v b pre run
  cases run
  refine ⟨?_,?_⟩
  · apply CurrentSlots.fields_transport pre.1.1
    simp only [CurrentSlots.fields]
    apply Prod.ext
    · simp only [Option.map_map,Function.comp_def]
    · apply Prod.ext
      · funext target; simp only [Option.bind_map,Function.comp_def]
      · funext kid
        simp only [Leanux.Proofs.WG.Queues.RxCredits.keyWords,Option.bind_map,Function.comp_def]
  · intro d device
    cases before : w.dev with
    | none => simp [before] at device
    | some old =>
      simp only [before,Option.map_some,Option.some.injEq] at device
      subst d
      exact pre.1.2 old before

end Leanux.Proofs.WG.Index.TimerCore
