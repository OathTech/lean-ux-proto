import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketFrontFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxPostSocket

/-! Product-world points for the fixed socket front. The continuation keeps
the original socket entry world, including when its route or cache work is
resumed at a later native source point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketFront
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points CompletionFirstTerminal SocketInterior
abbrev History := List CausalJournal.Event
variable {packet : RunWitness DataPacket}

inductive RootPoint (pid : PeerId) (packet : RunWitness DataPacket) (peer : RunWitness Peer) (ipv4 : Bool) :
    World → History → World → History → Prop where
  | source {w : World} {h : History} {site : Site} {v : WGWorld} {b : Ambient}
      {middle : List LifetimeEvent} {remaining : MixedM (Except Int SentDatagram)}
      (point : Point (canonical (endpoint peer) (some pid) packet.value.bytes packet.value.ds true ipv4)
        w.wg w.ambient (KeyAccess.project h) site v b middle remaining) :
      RootPoint pid packet peer ipv4 w h {w with wg:=v,ambient:=b}
        (h++(middle.drop (KeyAccess.project h).length).map KeyAccess.encode)

theorem RootPoint.remaining (point : RootPoint pid packet peer ipv4 w h u middle) :
    ∃remaining,runPrefix (FirstTerminal.focused (socketFront pid packet peer ipv4)) w h=runPrefix remaining u middle := by
  cases point with
  | @source site v b middle remaining point=>
      obtain ⟨suffix,extended⟩:=point.appends
      refine ⟨KeyAccess.observed remaining,?_⟩
      change runPrefix (TxAccountingAccess.observed _) _ _=_
      rw [TxAccountingAccess.observed_eq,extended,List.drop_left]
      exact KeyAccess.observed_remainder _ _ _ _ _ _ suffix (by rw [←extended];exact point.run) point.remaining_appends

theorem focused_receipt (body : PrefixM Completion.Event α) (appends : Appends body)
    (record : RunWitness α → Completion.Event) :
    FirstTerminal.focused (receiptObserved body record)=
      receiptObserved (FirstTerminal.focused body) (FirstTerminal.encode ∘ record) := by
  funext w h
  obtain ⟨suffix,grown⟩:=appends w (h.filterMap CausalJournal.completion?)
  change (runPrefix (receiptObserved body record) w (h.filterMap CausalJournal.completion?) |>.1,
    h++List.map FirstTerminal.encode ((runPrefix (receiptObserved body record) w
      (h.filterMap CausalJournal.completion?)).2.drop (h.filterMap CausalJournal.completion?).length))=
    runPrefix (receiptObserved (FirstTerminal.focused body) (FirstTerminal.encode ∘ record)) w h
  rw [runPrefix_receiptObserved,runPrefix_receiptObserved]
  rw [show runPrefix (FirstTerminal.focused body) w h=
    ((runPrefix body w (h.filterMap CausalJournal.completion?)).1,
      h++((runPrefix body w (h.filterMap CausalJournal.completion?)).2.drop
        (h.filterMap CausalJournal.completion?).length).map FirstTerminal.encode) from rfl]
  cases performed : runPrefix body w (h.filterMap CausalJournal.completion?) with
  | mk result last=>
      change (runPrefix body w (h.filterMap CausalJournal.completion?)).2=_ at grown
      rw [performed] at grown
      cases result with
      | error reason=>rfl
      | ok pair=>
          obtain ⟨value,v⟩:=pair
          simp only [show last=h.filterMap CausalJournal.completion?++suffix from grown,
            List.append_assoc,List.drop_left,List.map_append,List.map_cons,List.map_nil,Function.comp_apply]

def resume (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (peer : RunWitness Peer)
    (ipv4 : Bool) (origin : World) (front : PrefixM CausalJournal.Event (Except Int SentDatagram)) :
    PrefixM CausalJournal.Event Int :=
  receiptObserved (front >>= TxSocket.resultStep)
    (fun run=>.old (.socket ⟨pid,skb,packet,peer,ipv4,{run with before:=origin}⟩))

theorem resume_source (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (peer : RunWitness Peer)
    (ipv4 : Bool) (w : World) (h : History) :
    runPrefix (FirstTerminal.focused (Completion.socket pid skb packet peer ipv4)) w h=
      runPrefix (resume pid skb packet peer ipv4 w (FirstTerminal.focused (socketFront pid packet peer ipv4))) w h := by
  have appendResult (result : Except Int SentDatagram) : Appends (resultPrefix result) := by
    cases result with
    | error code=>exact Appends.pure _
    | ok sent=>exact Appends.bind (Appends.lift _) (fun _=>Appends.pure _)
  have appended : Appends (socketBody pid packet peer ipv4) := by
    rw [body_factor]
    exact Appends.bind (Appends.focus _ _ _) appendResult
  change runPrefix (FirstTerminal.focused (receiptObserved (socketBody pid packet peer ipv4) _)) w h=_
  rw [focused_receipt _ appended,body_factor,
    TxAccounting.focused_bind (body:=socketFront pid packet peer ipv4) (Appends.focus _ _ _) appendResult]
  unfold resume
  rw [runPrefix_receiptObserved,runPrefix_receiptObserved]
  rfl

theorem resume_run_equal {left right : PrefixM CausalJournal.Event (Except Int SentDatagram)}
    (same : runPrefix left w h=runPrefix right u middle) :
    runPrefix (resume pid skb packet peer ipv4 origin left) w h=
      runPrefix (resume pid skb packet peer ipv4 origin right) u middle := by
  unfold resume
  rw [runPrefix_receiptObserved,runPrefix_receiptObserved]
  rw [Scheduler.bind_run_equal TxSocket.resultStep same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketFront
