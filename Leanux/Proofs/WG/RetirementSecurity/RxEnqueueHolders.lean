import Leanux.Proofs.WG.RetirementSecurity.RxStoreHolders
import Leanux.Proofs.WG.Queues.RxIngressCarrier

/-! Full native RX enqueue consumes the saved key reference at peer-queue
admission, including EPIPE, and leaves it temporary on ENOSPC. The existing
source-derived complete device effect supplies the exact endpoint. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem HolderAccount.enqueue_rx_native {id : SkbId}
    (account : HolderAccount (allocation :: temporary) w)
    (device : w.dev = some d) (packet : d.rxSkbs[id]? = some pkt)
    (peer : d.peers[pkt.peer]? = some p)
    (loan : receiveLoan w pkt.peer id = some ⟨.receive pkt.peer id,allocation⟩)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeerRx id).run w).run a = .ok ((ret,v),b)) :
    (ret = -WG.ENOSPC ∧ HolderAccount (allocation :: temporary) v ∧ holderStore v = holderStore w) ∨
      ((ret = 0 ∨ ret = -WG.EPIPE) ∧ HolderAccount temporary v) := by
  obtain ⟨returns,cpu,store⟩ := Queues.RxCredits.enqueue_effect device packet peer a b run
  have finalDevice := congrArg WGStoreView.dev store
  change v.dev = some (Queues.RxCredits.enqueueDevice d id pkt p ret cpu) at finalDevice
  let marked := Packets.update w (fun current =>
    {current with rxSkbs := current.rxSkbs.insert id {pkt with state := .uncrypted}})
  have markRun : ((setRxSkb id (fun p => {p with state := .uncrypted})).run w).run a =
      .ok (((),marked),a) := Packets.setRxSkb_run w a d id pkt _ device packet
  have markFields := (ProjectedAction.iff_run_ambient _ _ _).mp
    (setRx_holderStore id (fun p => {p with state := .uncrypted}) (fun _ => rfl))
    w a () marked a markRun
  have markAccount := account.store markFields
  have markDevice : marked.dev = some {d with rxSkbs := d.rxSkbs.insert id {pkt with state := .uncrypted}} := by
    simp [marked,Packets.update,device]
  by_cases refused : ret = -WG.ENOSPC
  · have fields : holderStore v = holderStore marked := by
      simp [holderStore,Origins.view,peersAt,packetKeyWords,finalDevice,markDevice,
        Queues.RxCredits.enqueueDevice,refused,WG.ENOSPC,Leanux.ENOSPC]
    exact Or.inl ⟨refused,markAccount.store fields,fields.trans markFields⟩
  · have accepted : ret = 0 ∨ ret = -WG.EPIPE := by
      rcases returns with zero | full | pipe
      · exact Or.inl zero
      · exact False.elim (refused full)
      · exact Or.inr pipe
    let installed := replacePeer marked
      {d with rxSkbs := d.rxSkbs.insert id {pkt with state := .uncrypted}}
      pkt.peer {p with rxQueue := p.rxQueue.enqueue id}
    have found : peerAt marked pkt.peer = some p := by simp [peerAt,markDevice,peer]
    have markedLoan : receiveLoan marked pkt.peer id = some ⟨.receive pkt.peer id,allocation⟩ :=
      ((loan_store markFields).2.2 pkt.peer id).trans loan
    have setRun : ((setPeer pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).run marked).run a =
        .ok (((),installed),a) := by simp [setPeer,modifyDev,installed,replacePeer,markDevice]
    have installedAccount := markAccount.enqueue_rx found markedLoan a a setRun
    have notFull : ret ≠ -Leanux.ENOSPC := refused
    have fields : holderStore v = holderStore installed := by
      simp only [holderStore,Origins.view,peersAt,packetKeyWords,installed,replacePeer,
        finalDevice,Option.map_some,Option.bind_some,Queues.RxCredits.enqueueDevice,
        ite_eq_right notFull]
    exact Or.inr ⟨accepted,installedAccount.store fields⟩

end Leanux.Proofs.WG.RetirementSecurity
