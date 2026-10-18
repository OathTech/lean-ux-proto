import Leanux.Proofs.WG.Index.TransmitCoreModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TransmitCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem store_rich {α : Type} (action : WG.M α) (same : SameWGStore action)
    (entry : WGWorld) : Ensures action (StagingRich.Frame entry) (fun _=>StagingRich.Frame entry) := by
  intro w a result v b pre run
  have effect := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact StagingRich.same_device entry w v pre
    (congrArg WGStoreView.dev effect) (congrArg WGStoreView.keypairCounter effect)

theorem modifyPeer_rich (pid : PeerId) (f : Peer→Peer)
    (same : ∀p,StagingRich.PeerCell (f p)=StagingRich.PeerCell p) (entry : WGWorld) :
    Ensures (modifyPeer pid f) (StagingRich.Frame entry) (fun _=>StagingRich.Frame entry) := by
  apply StagingRich.readPeer entry pid
  intro p cell
  exact StagingRich.setPeer_rich entry pid (f p) (by simpa only [same] using cell)

theorem lookupDst_rich (family addr : Nat) (entry : WGWorld) :
    Ensures (lookupDst family addr) (StagingRich.Frame entry) (fun _=>StagingRich.Frame entry) := by
  intro w a result v b pre run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    exact StagingRich.same_device entry w v pre
      (congrArg WGStoreView.dev borrowed) (congrArg WGStoreView.keypairCounter borrowed)
  | some pid =>
    obtain ⟨d,p,device,resident,_,effect⟩ := borrowed
    have before : w.dev=some d := device
    have after : v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} :=
      congrArg WGStoreView.dev effect
    apply StagingRich.of_views entry w v ?_ ?_ ?_ ?_ pre
    · simp [before,after,TimerDiscipline.tableCursor]
    · funext target
      simpa only [StagingRich.peerMap,before,after,Option.bind_some] using congrFun
        (StagingRich.peerMap_write d pid p {p with refcount:=p.refcount+1} resident rfl) target
    · funext kid
      simp [StagingRich.keyMap,before,after]
    · exact congrArg WGStoreView.keypairCounter effect

theorem xmitTrim_rich (pid : PeerId) (entry : WGWorld) :
    Ensures (xmitTrim pid) (StagingRich.Frame entry) (fun _=>StagingRich.Frame entry) := by
  have kept : SameView richView (xmitTrim pid) := xmitTrim_view richView pid (by
    intro w d p device resident
    unfold richView
    simp only [device,Option.map_some]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · funext target
      simpa only [StagingRich.peerMap,device,Option.bind_some] using congrFun
        (StagingRich.peerMap_write d pid p {p with staged:=p.staged.drop 1} resident rfl) target
    · refine Prod.ext ?_ rfl
      funext kid
      simp only [StagingRich.keyMap,device,Option.bind_some])
  intro w a result v b pre run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp kept w a result v b run
  exact StagingRich.of_views entry w v (congrArg Prod.fst same)
    (congrArg (fun s=>s.2.1) same) (congrArg (fun s=>s.2.2.1) same)
    (congrArg (fun s=>s.2.2.2) same) pre

theorem xmitSplice_rich (pid : PeerId) (packets : List WG.Packet) (entry : WGWorld) :
    Ensures (xmitSplice pid packets) (StagingRich.Frame entry) (fun _=>StagingRich.Frame entry) := by
  unfold xmitSplice
  rw [getPeer_twice]
  exact modifyPeer_rich pid (fun p=>{p with staged:=p.staged++packets}) (fun _=>rfl) entry

theorem ready_product_store {w v : World}
    (same : productStoreView v=productStoreView w)
    (pre : TimerCore.Ready w.wg) : TimerCore.Ready v.wg := by
  have device : v.wg.dev=w.wg.dev := congrArg (fun s : ProductStore43=>s.2.2.2.dev) same
  refine ⟨CurrentSlots.fields_transport pre.1 ?_,Reached.core_device device pre.2⟩
  unfold CurrentSlots.fields Queues.RxCredits.keyWords
  rw [device]

end Leanux.Proofs.WG.Index.TransmitCore
