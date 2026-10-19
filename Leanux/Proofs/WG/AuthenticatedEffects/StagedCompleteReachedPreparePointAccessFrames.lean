import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointSource

/-! Read-derived requirements for the only preparation writes that can
change a packet/peer slot. No arbitrary cached setter receives a quiet frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal RetirementSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def Access.Entry : {E α : Type} → {body : WGPrefix E α} → Access body → WGWorld → Prop
  | _,_,_,.writePeer pid p,w => ∃d q,w.dev=some d ∧ d.peers[pid]?=some q ∧
      p.internalId=q.internalId ∧ p.staged=q.staged ∧ p.txQueue=q.txQueue
  | _,_,_,.writeRx id _,w => ∃d q,w.dev=some d ∧ d.rxSkbs[id]?=some q
  | _,_,_,_,_ => True

theorem Access.native_frame {E α : Type} {body : WGPrefix E α}
    {w v : WGWorld} {a b : Ambient} {value : α}
    (token : Access body) (before : token.Entry w)
    (performed : (token.native.run w).run a=.ok ((value,v),b)) :
    StagedEntry.view v=StagedEntry.view w := by
  cases token with
  | readPeer pid => exact congrArg StagedEntry.view (Peers.getPeer_current _ _ _ _ _ _ performed).1
  | readKey id => exact (ProjectedAction.iff_run_ambient _ _ _).mp (ReceiveFrames.key_read id) _ _ _ _ _ performed
  | readRx id => exact congrArg StagedEntry.view (Packets.getRxSkb_current _ _ _ _ _ _ performed).1
  | writePeer pid p =>
      obtain ⟨d,q,device,resident,stamp,staged,queue⟩:=before
      change Except.ok (((),{w with dev:=w.dev.map fun (d : Device)=>{d with peers:=d.peers.insert pid p}}),a)=_ at performed
      rw [device] at performed
      cases performed
      exact Queued.replace_peer device resident stamp staged queue
  | writeKey id k =>
      have frame : SameView StagedEntry.view (setKeypair id k) := by
        intro initial
        unfold setKeypair
        apply ReceiveFrames.device <;> intro d <;> rfl
      exact (ProjectedAction.iff_run_ambient _ _ _).mp frame _ _ _ _ _ performed
  | writeRx id p =>
      obtain ⟨d,q,device,resident⟩:=before
      change Except.ok (((),{w with dev:=w.dev.map fun (d : Device)=>{d with rxSkbs:=d.rxSkbs.insert id p}}),a)=_ at performed
      rw [device] at performed
      cases performed
      exact CompleteDecrypt.replace_rx device resident p

/-- The getter establishes actual residency, not merely a historical ID. -/
theorem read_rx_resident {id : SkbId} {p : RxPacket} {w v : WGWorld} {a b : Ambient} (performed : (getRxSkb id).run w a=.ok ((p,v),b)) :
    v=w ∧ b=a ∧ ∃d,w.dev=some d ∧ d.rxSkbs[id]?=some p :=
  Packets.getRxSkb_current _ _ _ _ _ _ performed

/-- The exact cached peer comes from this getter at this native source cut. -/
theorem read_peer_resident {pid : PeerId} {p : Peer} {w v : WGWorld} {a b : Ambient} (performed : (getPeer pid).run w a=.ok ((p,v),b)) :
    v=w ∧ b=a ∧ ∃d,w.dev=some d ∧ d.peers[pid]?=some p :=
  Queues.getPeer_normal _ _ _ _ _ _ performed

/-- RX payload/state replacement retains the entire cached peer record,
including the staged and TX queues used at the later publication setter. -/
theorem write_rx_peer {w v : WGWorld} {d : Device} {pid : PeerId} {p : Peer}
    {id : SkbId} {next : RxPacket} {a b : Ambient} {value : Unit} (device : w.dev=some d) (peer : d.peers[pid]?=some p)
    (performed : (modifyDev (fun d=>{d with rxSkbs:=d.rxSkbs.insert id next})).run w a=
      .ok ((value,v),b)) :
    ∃e,v.dev=some e ∧ e.peers[pid]?=some p := by
  change Except.ok (((),{w with dev:=w.dev.map fun (d : Device)=>{d with rxSkbs:=d.rxSkbs.insert id next}}),a)=_ at performed
  rw [device] at performed
  cases performed
  exact ⟨_,rfl,peer⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
