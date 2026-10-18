import Leanux.Proofs.WG.Index.TxDisposalCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem selected_drop_boundary (cs : Ledger) (loans : Reservations)
    (holders : DurableHolders) (chosen : TxHandoff) (rest : List TxHandoff)
    (w : WGWorld) (d : Device) (pid : PeerId) (p : Peer)
    (q : PrevQueue (List SkbId))
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (entry : DeviceBoundary.Entry cs loans w ∧ Reached.Core w)
    (funded : holders.Funded cs loans w)
    (stable : StableRx cs w)
    (selected : TxSelected holders.tx pid chosen rest)
    (drop : q.all=p.txQueue.all.tail) :
    let updated := {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=q}}}
    (holders.withoutTx rest).Funded cs (chosen.owner::loans) updated ∧
      StableRx cs updated ∧ BaseCoherence.Inv updated ∧
      ConfiguredIdentity.Inv updated ∧ Reached.Core updated := by
  let updated : WGWorld :=
    {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=q}}}
  have input := funded.tx_input stable selected
  have after : ClearWork.Inv cs (chosen.owner::((holders.withoutTx rest).owners++loans)) updated :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.queue_update)
      input device resident q
  have passive : passiveView updated=passiveView w := by simp [updated,passiveView,device]
  have sends : sendView updated=(sendView w).map (·++ ([] : List PeerId)) := by
    simp [updated,sendView,device]
  have others : ∀other,other≠pid → handoffTxView updated other=handoffTxView w other := by
    intro other ne
    simp [updated,handoffTxView,device,Std.TreeMap.getElem?_insert,Ne.symm ne]
  have source : handoffTxView w pid=some (holders.items pid) := by
    have actual : handoffTxView w pid=some p.txQueue.all := by simp [handoffTxView,device,resident]
    rw [←funded.aligned.tx pid p.txQueue.all actual]
    exact actual
  have debit : ∀before ending,handoffTxView w pid=some before →
      handoffTxView updated pid=some ending → ending=before.tail := by
    intro before ending hb he
    have beforeEq : p.txQueue.all=before := by simpa [handoffTxView,device,resident] using hb
    have afterEq : q.all=ending := by simp [updated,handoffTxView] at he; exact he
    exact afterEq.symm.trans (drop.trans (congrArg List.tail beforeEq))
  have aligned := (pinned_const _private.Leanux.Proofs.WG.Queues.TxHolderAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.aligned_tx_paid)
    funded.aligned selected (show ({} : HandoffDelta).tx=[] from rfl) source passive sends others debit
  have aligned' : (holders.withoutTx rest).Aligned updated := by
    simpa only [absorb,List.append_nil] using aligned
  have funded' : (holders.withoutTx rest).Funded cs (chosen.owner::loans) updated :=
    ⟨aligned',WorkReservations.carrier_loans_perm after.1 List.perm_middle.symm⟩
  have fields : ConfigurationIndex.fields updated=ConfigurationIndex.fields w := by
    simpa [ConfigurationIndex.fields,updated,device] using congrArg some
      (ConfigurationIndex.deviceFields_peerWrite d pid p {p with txQueue:=q} resident rfl)
  have cfgEq : ConfiguredIdentity.view updated=ConfiguredIdentity.view w := by
    simp only [ConfiguredIdentity.view,updated,device,Option.map_some]
    congr 1
    unfold ConfiguredIdentity.state
    congr 1
    funext target
    by_cases same : pid=target
    · subst target
      simp [resident,ConfiguredIdentity.cell]
    · simp [Std.TreeMap.getElem?_insert,same]
  have configured : ConfiguredIdentity.Inv updated := by
    intro state present
    exact entry.1.2.2 state (cfgEq.symm.trans present)
  exact ⟨funded',after.2,BaseCoherence.transport entry.1.2.1
    (by simp [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device]),
    configured,ConfigurationIndex.fields_core w updated fields entry.2⟩

theorem queue_current (history : List SessionOrigin.Receipt)
    (w : WGWorld) (d : Device) (pid : PeerId) (p : Peer) (q : PrevQueue (List SkbId))
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (entry : CurrentLifecycle.Inv history w) :
    CurrentLifecycle.Inv history {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=q}}} := by
  let updated : WGWorld := {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=q}}}
  have cfgEq : ConfiguredIdentity.view updated=ConfiguredIdentity.view w := by
    simp only [ConfiguredIdentity.view,updated,device,Option.map_some]
    congr 1
    unfold ConfiguredIdentity.state
    congr 1
    funext target
    by_cases same : pid=target
    · subst target
      simp [resident,ConfiguredIdentity.cell]
    · simp [Std.TreeMap.getElem?_insert,same]
  refine ⟨fun state present=>entry.1 state (cfgEq.symm.trans present),?_⟩
  apply entry.2.retain
  apply CurrentIdentity.retains_of_configured_view _ cfgEq
  change Origins.RetainsView (Origins.view w) (Origins.view updated)
  have material : Origins.view updated=Origins.view w := by simp [Origins.view,updated,device]
  rw [material]
  exact Origins.RetainsView.refl _

theorem peek_boundary (cs : Ledger) (loans : Reservations)
    (w : WGWorld) (d : Device) (pid : PeerId) (p : Peer) (q : PrevQueue (List SkbId))
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (same : q.all=p.txQueue.all)
    (entry : DeviceBoundary.Entry cs loans w ∧ Reached.Core w) :
    DeviceBoundary.Entry cs loans {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=q}}} ∧
    Reached.Core {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=q}}} := by
  let updated : WGWorld := {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=q}}}
  obtain ⟨holders,funded,stable⟩ := entry.1.1
  have account := (pinned_const _private.Leanux.Proofs.WG.Queues.TxHolderStep.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.peek_install)
    funded stable device resident q same
  have cfgEq : ConfiguredIdentity.view updated=ConfiguredIdentity.view w := by
    simp only [ConfiguredIdentity.view,updated,device,Option.map_some]
    congr 1
    unfold ConfiguredIdentity.state
    congr 1
    funext target
    by_cases eq : pid=target
    · subst target
      simp [resident,ConfiguredIdentity.cell]
    · simp [Std.TreeMap.getElem?_insert,eq]
  have fields : ConfigurationIndex.fields updated=ConfigurationIndex.fields w := by
    simpa [ConfigurationIndex.fields,updated,device] using congrArg some
      (ConfigurationIndex.deviceFields_peerWrite d pid p {p with txQueue:=q} resident rfl)
  exact ⟨⟨⟨holders,account⟩,BaseCoherence.transport entry.1.2.1
      (by simp [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device]),
      fun state found=>entry.1.2.2 state (cfgEq.symm.trans found)⟩,
    ConfigurationIndex.fields_core w updated fields entry.2⟩

end Leanux.Proofs.WG.Index.CryptCore
