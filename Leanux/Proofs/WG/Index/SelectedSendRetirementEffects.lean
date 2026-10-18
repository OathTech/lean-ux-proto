import Leanux.Proofs.WG.Index.SelectedSendRetirementModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- Queue selection transfers one existing occurrence; the paired pending
write then reuses the landed carrier-update and holder-alignment contracts. -/
theorem sendPrepared_funded
    (holders : DurableHolders) (cs : Ledger) (loans : Reservations)
    (pid : PeerId) (paid : Owner) (rest : Reservations)
    (selected : WorkReservations.Selected holders.send pid paid rest)
    (w : WGWorld) (d : Device) (p : Peer) (device : w.dev = some d)
    (resident : d.peers[pid]? = some p)
    (funded : holders.Funded cs loans w) (stable : StableRx cs w) :
    (holders.withoutSend rest).Funded cs (paid :: loans)
        {w with dev := some (sendPreparedDevice d pid p)} ∧
      StableRx cs {w with dev := some (sendPreparedDevice d pid p)} := by
  let taken := sendTaken w pid
  let dequeued := {d with sendWorkQueue := d.sendWorkQueue.erase pid}
  let updated := {p with handshakePending := dequeued.sendWorkQueue.contains pid}
  have hd : taken.dev = some dequeued := by simp [taken,sendTaken,device,dequeued]
  have hp : dequeued.peers[pid]? = some p := resident
  have credit := funded.take_send selected
  have stillStable : StableRx cs taken := stable.view (by
    unfold taken sendTaken stableView Queues.RxRing.nativeCell rxView
    cases w.dev <;> rfl)
  have pending := (pinned_const _private.Leanux.Proofs.WG.Queues.RxClearWork.«0».Leanux.Proofs.WG.Queues.RxCredits.ClearWork.peer_update)
    ⟨credit.carriers,stillStable⟩ hd hp updated rfl rfl rfl rfl (fun _ h => h)
  have frame : Frame taken {taken with dev := some {dequeued with peers := dequeued.peers.insert pid updated}} := by
    refine ⟨?_,?_,?_⟩
    · simp [passiveView,hd]
    · simp [sendView,hd]
    · intro q batches found
      by_cases same : pid = q
      · subst q
        simpa [handoffTxView,hd,hp,updated] using found
      · simpa [handoffTxView,hd,Std.TreeMap.getElem?_insert,same] using found
  exact ⟨⟨credit.aligned.frame frame,pending.1⟩,pending.2⟩

/-- The selected stamped loan supplies the weak caller condition needed by
the actual creator, including a nullable self word. No live-peer premise is
imposed, so an inline worker of an already retired peer remains in scope. -/
theorem funded_send_handshakeCompatible
    (holders : DurableHolders) (cs : Ledger) (paid : Owner) (loans : Reservations)
    (w : WGWorld) (configured : ConfiguredIdentity.Inv w)
    (funded : holders.Funded cs (paid :: loans) w)
    (coherent : ∀ d, w.dev = some d → HashedOwnersCoherent d) :
    ∀ d, w.dev = some d → HandshakeCompatible paid.slot d := by
  have charged : 0 < demand cs (holders.owners ++ (paid :: loans)) paid := by
    simp only [demand,List.count_append,List.count_cons_self]
    omega
  obtain ⟨old,found,bound⟩ := protected_resident funded.carriers.funded charged
  obtain ⟨original,device,_,resident,_⟩ := resident_fields found
  intro d present
  have same : original = d := Option.some.inj (device.symm.trans present)
  subst original
  refine ⟨coherent d present,?_⟩
  intro p stored
  have equal : p = old := Option.some.inj (stored.symm.trans resident)
  subst p
  have identity := configured (ConfiguredIdentity.state d) (by
    simp [ConfiguredIdentity.view,present])
  refine ⟨identity.self paid.slot (ConfiguredIdentity.cell old) ?_,by omega⟩
  simp [ConfiguredIdentity.state,resident]

end Leanux.Proofs.WG.Index
