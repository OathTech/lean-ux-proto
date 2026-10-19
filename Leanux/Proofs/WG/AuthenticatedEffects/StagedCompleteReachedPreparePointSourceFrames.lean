import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointFramed

/-! Actual getter-derived slot and cache frames for the canonical setters.
These obligations are discharged at their original source prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal RetirementSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {w v : WGWorld} {a b : Ambient}

theorem setRx_framed (id : SkbId) (f : RxPacket → RxPacket) (h : List LifetimeEvent) :
    Framed (setRx id f) w a h := by
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro packet v b middle performed
  have native := (Access.normal (.readRx id) performed).1
  obtain ⟨rfl,rfl,d,device,resident⟩:=read_rx_resident native
  exact ⟨d,packet,device,resident⟩

theorem refcount_same (count : Nat) : SameView (fun w : WGWorld=>w) (refcountInc count : WG.M Unit) := by
  intro initial
  change Preserves (fun w=>w=initial) _
  unfold refcountInc
  simp only [branch,branchCmp,unsupported]
  repeat' first | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _) | rx_retention_step

theorem peerGet_framed (pid : PeerId) (h : List LifetimeEvent) :
    Framed (peerGet pid) w a h := by
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro ignored u c middle noop
  cases noop
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro p v b last read
  obtain ⟨rfl,rfl,d,device,resident⟩:=read_peer_resident (Access.normal (.readPeer pid) read).1
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro ignored u c final increment
  have native : (refcountInc p.refcount : WG.M Unit).run v b=.ok ((ignored,u),c) := congrArg Prod.fst increment
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (refcount_same p.refcount) _ _ _ _ _ native
  subst u
  exact ⟨d,p,device,resident,rfl,rfl,rfl⟩

/-- A successful observed RX setter carries the exact peer cache across both
its original getter and its original slot write. -/
theorem setRx_peer {id : SkbId} {f : RxPacket → RxPacket} {pid : PeerId} {p : Peer}
    {d : Device} {h last : List LifetimeEvent} {result : Unit}
    (device : w.dev=some d) (peer : d.peers[pid]?=some p)
    (performed : runWGPrefix (setRxSkbPrefix id f) w a h=(.ok ((result,v),b),last)) :
    ∃e,v.dev=some e ∧ e.peers[pid]?=some p := by
  change runStatePrefix _ w a h = _ at performed
  rw [setRxSkbPrefix,runStatePrefix_bind] at performed
  cases front : runStatePrefix (getRxSkbPrefix id) w a h with
  | mk out middle =>
      rw [front] at performed
      cases out with
      | error reason => cases performed
      | ok out =>
          obtain ⟨⟨packet,u⟩,c⟩:=out
          obtain ⟨rfl,rfl,_,_,_⟩:=read_rx_resident (Access.normal (.readRx id) front).1
          exact write_rx_peer device peer (Access.normal (.writeRx id (f packet)) performed).1

/-- Publication uses the peer returned by its actual getter, through the
actual RX setter. The write input is therefore funded by that cached record;
no arbitrary peer setter is treated as quiet. -/
theorem publication_write_entry {pid : PeerId} {p : Peer} {id : SkbId} {f : RxPacket→RxPacket}
    {u : WGWorld} {c : Ambient} {h middle last : List LifetimeEvent} {result : Unit}
    (read : runWGPrefix (getPeerMixed pid) w a h=(.ok ((p,u),c),middle))
    (write : runWGPrefix (setRxSkbPrefix id f) u c middle=(.ok ((result,v),b),last)) :
    (Access.writePeer pid {p with napiScheduled:=true}).Entry v := by
  have native : (getPeer pid).run w a=.ok ((p,u),c) :=
    (getPeerMixed_erases pid w a h).symm.trans (congrArg Prod.fst read)
  obtain ⟨rfl,rfl,d,device,resident⟩:=read_peer_resident native
  obtain ⟨e,after,peer⟩:=setRx_peer device resident write
  exact ⟨e,p,after,peer,rfl,rfl,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
