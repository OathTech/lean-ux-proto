import Leanux.Proofs.WG.RetirementSecurity.HolderConsumeAcquired
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeepalive

/-! An actual acquired peer stays nonfinal through a closed TX/send handoff.
The source's exact count equation is used only for peer protection; it does
not supply any key reference credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConsume
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
variable {selected : PeerId}

theorem Strong.view (before : Strong pid w) (same : peerView v = peerView w) : Strong pid v := by
  simpa only [Strong,same] using before

theorem Strong.transfer (before : Strong pid w) (step : Transfer w v) : Strong pid v := by
  obtain ⟨delta,step⟩ := step
  cases device : w.dev with
  | none => simp [Strong,peerView,device] at before
  | some d =>
    cases stored : d.peers[pid]? with
    | none => simp [Strong,peerView,device,stored] at before
    | some p =>
      have count : 1 < p.refcount := by simpa [Strong,peerView,device,stored] using before
      have epoch := congrArg Prod.fst step.base
      cases final : v.dev with
      | none => simp [baseView,device,final] at epoch
      | some e =>
        have sameEpoch : e.ifindex = d.ifindex := by simpa [baseView,device,final] using epoch
        have fields := congrFun (congrArg Prod.snd step.base) pid
        cases resident : e.peers[pid]? with
        | none => simp [baseView,device,final,stored,resident] at fields
        | some q =>
          have sameStamp : q.internalId = p.internalId := by
            have pair : q.internalId = p.internalId ∧ q.rxQueue = p.rxQueue := by
              simpa [baseView,device,final,stored,resident] using fields
            exact pair.1
          have budget := step.count ⟨d.ifindex,pid,p.internalId⟩
          simp only [List.count_nil,Nat.add_zero] at budget
          have old : balance w ⟨d.ifindex,pid,p.internalId⟩ = p.refcount := by
            simp [balance,RxCredits.resident,device,stored]
          have now : balance v ⟨d.ifindex,pid,p.internalId⟩ = q.refcount := by
            simp [balance,RxCredits.resident,final,resident,sameEpoch,sameStamp]
          rw [old,now] at budget
          simp only [Strong,peerView,final,Option.bind_some,resident,Option.map_some,Option.getD_some]
          omega

theorem strong_frame {action : WG.M α} (same : SameView peerView action) :
    Preserves (Strong selected) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.view ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem peers_store {action : WG.M α} (same : SameWGStore action) : SameView peerView action :=
  same.of_factor (fun s => peerView {dev:=s.dev}) peerView (fun _ => rfl)

theorem peers_update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p,(f p).internalId=p.internalId)
    (count : ∀ p,(f p).refcount=p.refcount)
    (rx : ∀ p,(f p).rxQueue=p.rxQueue) :
    SameView peerView (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,getter,setter⟩ := run
  obtain ⟨rfl,rfl,d,device,stored⟩ := getPeer_normal pid w u p a c getter
  cases setter
  apply Prod.ext
  · simp [peerView,device]
  · funext other
    by_cases same : pid=other
    · subst other
      simp [peerView,device,stored,stamp,count,rx]
    · simp [peerView,device,Std.TreeMap.getElem?_insert,same]

theorem peers_update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀ p,(f p).internalId=p.internalId)
    (count : ∀ p,(f p).refcount=p.refcount)
    (rx : ∀ p,(f p).rxQueue=p.rxQueue)
    (rest : ∀ x,Preserves (fun w => peerView w = initial) (tail x)) :
    Preserves (fun w => peerView w = initial) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind ((peers_update pid f stamp count rx).wp (·=initial)) rest

macro "strong_peer_step " initial:term : tactic => `(tactic| first
  | (receive_update_head setPeer; apply (peers_update _ _ ?_ ?_ ?_).wp (·=$initial) <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     apply peers_update_bind
     · intro p; rfl
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact (peers_store getDev_sameWGStore).wp (·=$initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; exact stop _)
  | rxstack_preserves_join
  | rx_retention_step)

theorem session_peers (pid : PeerId) : SameView peerView (beginSession pid) :=
  (SessionCarrier.beginSession_view pid).factor (fun s => s.1.1)

end Leanux.Proofs.WG.RetirementSecurity.HolderConsume
