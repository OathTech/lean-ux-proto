import Leanux.Proofs.WG.Index.PollCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem peek_view_index_variant (pid : PeerId) :
    Preserves TimerCore.Ready (peekRxQueue pid) := by
  unfold peekRxQueue
  have read : Preserves TimerCore.Ready (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b pre run
    exact (getPeer_normal pid w v p a b run).1 ▸ pre
  apply preserves_bind read
  intro p
  apply preserves_bind (store_ready (prevQueuePeek_sameWGStore p.rxQueue))
  intro result
  have update : Preserves TimerCore.Ready
      (do let q←getPeer pid; setPeer pid {q with rxQueue:=result.2}) :=
    peer_update_ready pid (fun p=>{p with rxQueue:=result.2}) (fun _=>rfl) (fun _=>rfl)
  simpa only [bind_assoc] using preserves_bind update (fun _=>preserves_pure result.1)

theorem drop_ready (pid : PeerId) : Preserves TimerCore.Ready (dropRxQueue pid) := by
  unfold dropRxQueue
  rw [getPeer_twice]
  exact peer_update_ready pid (fun p=>{p with rxQueue:=p.rxQueue.dropPeeked}) (fun _=>rfl) (fun _=>rfl)

theorem complete_ready (pid : PeerId) : Preserves TimerCore.Ready (completeRxQueue pid) :=
  peer_update_ready pid (fun p=>{p with napiScheduled:=false}) (fun _=>rfl) (fun _=>rfl)

theorem counterValidate_preserves_index_variant (kid : KeypairId) (nonce : Nat) :
    Preserves Reached.Core (counterValidate kid nonce) := by
  have getter : Hoare (getKeypair kid) Reached.Core
      (fun k w=>Reached.Core w ∧ keyCell w kid=some (k.peer,k.refcount)) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b pre run
    obtain ⟨rfl,_,d,device,resident⟩ := KeyTimes.getKeypair_return kid w v k a b run
    exact ⟨pre,by simp [keyCell,device,resident]⟩
  unfold counterValidate
  apply hoare_bind _ _ getter
  intro k
  let P := fun w=>Reached.Core w ∧ keyCell w kid=some (k.peer,k.refcount)
  have setter (counter : ReplayCounter) :
      Preserves P (setKeypair kid {k with receivingCounter:=counter}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    obtain ⟨old,stored,fields⟩ := Option.map_eq_some_iff.mp pre.2
    obtain ⟨d,device,resident⟩ := Option.bind_eq_some_iff.mp stored
    cases run
    refine ⟨?_,?_⟩
    · intro f found
      simp only [device,Option.map_some,Option.some.injEq] at found
      subst f
      exact key_write_core d kid old {k with receivingCounter:=counter} resident
        fields.symm (pre.1 d device)
    · simp [keyCell,device]
  apply hoare_consequence (P:=P) (Q:=fun _=>P) ?_ (fun _ h=>h) (fun _ _ h=>h.1)
  simp (config := {zeta := false}) only [WG.orM,Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head setKeypair; exact setter _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem counter_ready (kid : KeypairId) (nonce : Nat) :
    Preserves TimerCore.Ready (counterValidate kid nonce) :=
  ReceiveCompletion.ready_join _ (CurrentSlots.counterValidate_preserves kid nonce)
    (counterValidate_preserves_index_variant kid nonce)

theorem ready_ready (first : Option SkbId) :
    Preserves TimerCore.Ready
      (WG.andM (branch .rxPollPacket first.isSome) do
        let some f:=first | invariant "unreachable"
        branch .rxPollNotUncrypted ((←getRxSkb f).state != .uncrypted)) := by
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head getRxSkb; exact packet_ready (SkbStore.getRx _))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ TimerCore.Ready)
    | rx_retention_step

end Leanux.Proofs.WG.Index.PollCore
