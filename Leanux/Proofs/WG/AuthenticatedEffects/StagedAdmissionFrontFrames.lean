import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionCheckpoint
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFramesNative
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrontFrames

/-! Exact queue frames around the front's actual counted-disposal cuts.
Reference release itself is handled conditionally at its native receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
set_option maxHeartbeats 600000
set_option pp.structureInstances false

variable {history : List CausalJournal.Event} {ledger : Ledger}

theorem check (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Preserves (QueueInv history ledger) (Packets.txCheck family addr packets mtu) := by
  have errors := QueueNative.modify_device (history := history) (ledger := ledger)
    (fun d => {d with txErrors := d.txErrors+1}) (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves (QueueInv history ledger) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (QueueInv history ledger)
  routing_tx_source [Packets.txCheck,Packets.txHeaders] using [errors,ambient]
  all_goals exact hoare_liftAmbient _ _

theorem lookup (family addr : Nat) : Preserves (QueueInv history ledger) (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    exact before.views (by simp [Packets.epoch,same]) (by funext pid; simp [Staged.stagedAt,same])
  | some pid =>
    obtain ⟨d,p,device,resident,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} :=
      congrArg WGStoreView.dev after
    apply before.views (by simp [Packets.epoch,endpoint,device])
    funext other
    by_cases same : pid = other
    · subst other; simp [Staged.stagedAt,endpoint,device,resident]
    · simp [Staged.stagedAt,endpoint,device,Std.TreeMap.getElem?_insert,same]

theorem error (family : Nat) (first : Packet) (ret : Int) :
    Preserves (QueueInv history ledger) (Packets.txError family first ret) := by
  have loopback (sites : List HiddenSite) (raised : Bool) :
      Preserves (QueueInv history ledger) (loopbackSend sites raised) :=
    QueueNative.store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves (QueueInv history ledger) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (QueueInv history ledger)
  have routing {α : Type} (a : Net.M α) : Preserves (QueueInv history ledger) (monadLift a : WG.M α) :=
    QueueNative.store (liftRouting_sameWGStore a)
  have errors := QueueNative.modify_device (history := history) (ledger := ledger)
    (fun d => {d with txErrors := d.txErrors+1}) (fun _ => rfl) (fun _ => rfl)
  rxstack_preserves_source [Packets.txError,branch,skipCutSites] using [loopback,ambient,routing,errors]

theorem walk (packets : List Packet) (mtu : Nat) (acc : List Packet) :
    Preserves (QueueInv history ledger) (Packets.txWalk packets mtu acc) :=
  QueueNative.store (RxCredits.txWalk_kernel packets mtu acc)

theorem release_none (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (run : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer)) (value : r.value = none) :
    Packets.epoch r.after = Packets.epoch r.before ∧ Staged.stagedAt r.after = Staged.stagedAt r.before := by
  rcases r with ⟨result,w,v,a,b⟩
  dsimp only at value
  subst result
  change ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w).run a = .ok ((none,v),b) at run
  cases peer with
  | none =>
    simp [HandshakeSecurity.StagedDisposal.releaseCut,branch,AmbientM.branch] at run
    rcases run with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl⟩
  | some pid =>
    cases device : w.dev with
    | none =>
      simp [HandshakeSecurity.StagedDisposal.releaseCut,branch,AmbientM.branch,requireNotPending,
        getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [HandshakeSecurity.StagedDisposal.releaseCut,branch,AmbientM.branch,requireNotPending,
          getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        have lifted (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals simp [HandshakeSecurity.StagedDisposal.releaseCut,requireNotPending,getPeer,getDev,
            setPeer,modifyDev,refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,lifted,
            liftIndex_run,CounterWindow.branch_run,CounterWindow.branchCmp_run,device,resident,
            positive,nonzero,final,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
            CounterWindow.except_ok_bind,CounterWindow.except_pure,invariant,AmbientM.invariant,
            unsupported,AmbientM.unsupported] at run
          all_goals repeat' first | split at run | contradiction
          all_goals try simp [Except.map,StateT.run_map,StateT.run_modify,
            CounterWindow.except_ok_bind,CounterWindow.except_pure] at run
          all_goals rcases run with ⟨rfl,rfl⟩
          all_goals refine ⟨by simp [Packets.epoch,device],?_⟩
          all_goals
            funext other
            by_cases same : pid = other
            · subst other; simp [Staged.stagedAt,device,resident]
            · simp [Staged.stagedAt,device,Std.TreeMap.getElem?_insert,same]
        · have zero : p.refcount = 0 := by omega
          simp [HandshakeSecurity.StagedDisposal.releaseCut,requireNotPending,getPeer,getDev,
            setPeer,modifyDev,refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,device,resident,zero,StateT.run_bind,
            StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
            CounterWindow.except_pure,unsupported,AmbientM.unsupported] at run
          cases run

theorem release_finish (pid : PeerId) (p : Peer) :
    Preserves (QueueInv history ledger) (HandshakeSecurity.StagedDisposal.releaseFinish pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  cases pending : PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome) with
  | some t =>
    simp [HandshakeSecurity.StagedDisposal.releaseFinish,pending,invariant,AmbientM.invariant] at run
    cases run
  | none =>
    simp [HandshakeSecurity.StagedDisposal.releaseFinish,pending,retirePeerUnits,modifyAmbient] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact before.views rfl rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Native
