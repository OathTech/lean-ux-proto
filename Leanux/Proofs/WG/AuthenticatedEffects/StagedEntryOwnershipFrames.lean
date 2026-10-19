import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionMaterialFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceQueueContents
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationDisposalMaterialFrames

/-! Native front frames retain the allocation frontier, complete TX packet
records and actual owning queues. These facts support ownership at a stopped
checkpoint as well as at normal front return. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Ownership
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
set_option maxHeartbeats 600000

open RetirementSecurity RetirementSecurity.StagingOccurrences Queues.RxCredits

def view (w : WGWorld) := (geometry w,txQueueContents w)

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
    change (geometry v,txQueueContents v) = (geometry w,txQueueContents w)
    apply Prod.ext
    · simp only [geometry,Packets.snapshot,TxDisposition.txPackets,same]
    · funext owner
      simp only [txQueueContents,handoffTxView,same]
  | some pid =>
    obtain ⟨d,p,device,resident,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} :=
      congrArg WGStoreView.dev after
    change (geometry v,txQueueContents v) = (geometry w,txQueueContents w)
    apply Prod.ext
    · simp only [geometry,Packets.snapshot,Packets.deviceStore,device,endpoint,TxDisposition.txPackets,Option.bind_some]
    · funext other
      by_cases same : pid = other
      · subst other; simp [txQueueContents,handoffTxView,endpoint,device,resident]
      · simp [txQueueContents,handoffTxView,endpoint,device,Std.TreeMap.getElem?_insert,same]

theorem errors : SameView view (modifyDev fun d => {d with txErrors := d.txErrors+1}) := by
  apply SameView.product
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    repeat' staging_geometry_step initial
  · intro initial
    change Preserves (fun w => txQueueContents w = initial) _
    repeat' occurrence_contents_step initial

theorem check (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    SameView view (Packets.txCheck family addr packets mtu) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  have errors : Preserves (fun w => view w = initial)
      (modifyDev (fun d => {d with txErrors := d.txErrors+1})) :=
    Ownership.errors initial
  have ambient {α : Type} (a : AmbientM α) : Preserves (fun w => view w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  routing_tx_source [Packets.txCheck,Packets.txHeaders] using [errors,ambient]
  all_goals exact hoare_liftAmbient _ _

theorem error (family : Nat) (first : WG.Packet) (ret : Int) : SameView view (Packets.txError family first ret) := by
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
    Ownership.errors initial
  rxstack_preserves_source [Packets.txError,branch,skipCutSites] using [loopback,ambient,routing,errors]

theorem walk (packets : List WG.Packet) (mtu : Nat) (acc : List WG.Packet) :
    SameView view (Packets.txWalk packets mtu acc) := store (RxCredits.txWalk_kernel packets mtu acc)

theorem trim (pid : PeerId) : SameView view (xmitTrim pid) :=
  (trim_packet_geometry pid).product (contents_factor ((xmitTrim_protect pid).factor (fun s => s.2.2.1)))

theorem release_queues (target : Option PeerId) :
    SameView txQueueContents (HandshakeSecurity.StagedDisposal.releaseCut target) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases target with
  | none =>
    simp [HandshakeSecurity.StagedDisposal.releaseCut,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    rfl
  | some pid =>
    cases device : w.dev with
    | none =>
      simp [HandshakeSecurity.StagedDisposal.releaseCut,branch,AmbientM.branch,
        requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases stored : d.peers[pid]? with
      | none =>
        simp [HandshakeSecurity.StagedDisposal.releaseCut,branch,AmbientM.branch,
          requireNotPending,getPeer,getDev,device,stored,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        have lift (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [HandshakeSecurity.StagedDisposal.releaseCut,requireNotPending,getPeer,getDev,
              setPeer,modifyDev,refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
              lift,liftIndex_run,CounterWindow.branch_run,CounterWindow.branchCmp_run,
              device,stored,positive,nonzero,final,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
              CounterWindow.except_ok_bind,CounterWindow.except_pure,
              invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at run
          all_goals repeat' first | split at run | contradiction
          all_goals try simp [Except.map,StateT.run_map,StateT.run_modify,
            CounterWindow.except_ok_bind,CounterWindow.except_pure] at run
          all_goals rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
          all_goals funext owner
          all_goals by_cases same : pid = owner
          all_goals first
            | (subst owner; simp_all [txQueueContents,handoffTxView,PrevQueue.all])
            | simp [txQueueContents,handoffTxView,device,Std.TreeMap.getElem?_erase,
                Std.TreeMap.getElem?_insert,same]
        · have zero : p.refcount = 0 := by omega
          simp [HandshakeSecurity.StagedDisposal.releaseCut,requireNotPending,getPeer,getDev,
            setPeer,modifyDev,refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,device,stored,zero,StateT.run_bind,StateT.run_pure,
            StateT.run_monadLift,CounterWindow.except_ok_bind,CounterWindow.except_pure,
            unsupported,AmbientM.unsupported] at run
          cases run

theorem release (peer : Option PeerId) : SameView view (HandshakeSecurity.StagedDisposal.releaseCut peer) :=
  (release_packet_geometry peer).product (release_queues peer)

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

theorem splice (pid : PeerId) (packets : List WG.Packet) : SameView view (xmitSplice pid packets) := by
  apply SameView.product
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    unfold xmitSplice
    repeat' staging_geometry_step initial
  · exact contents_factor ((xmitSplice_protect pid packets).factor (fun s => s.2.2.1))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Ownership
