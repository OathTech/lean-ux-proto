import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalLabelled
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePublicationFrames

/-! Publication's only release is nonfinal by its own native borrow. This
source fact certifies quiet admission prefixes, independently of final-state
erasure and without framing the later counted refusal repayments as quiet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging.Creation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier
open HandshakeSecurity.StagedDisposal

variable (Good : List CausalJournal.Event→Prop)
variable (extend : ∀ h suffix,Good h→(∀ event∈suffix,birthPackets event=[] ∧ Quiet event)→Good (h++suffix))
include extend

theorem focused (body : TxDisposition.Obs α) : Driver.ProductHistorySafe Good (QueueHandoff.focused body) := by
  intro w h before
  obtain ⟨suffix,extended⟩ := Appends.focus CausalJournal.txEvent CausalJournal.txEvent? body w h
  have kept : Good (runPrefix (QueueHandoff.focused body) w h).2 := by
    change Good (h++_)
    apply extend _ _ before
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact ⟨rfl,fun _=>rfl⟩
  refine ⟨suffix,extended,kept,?_⟩
  cases result : (runPrefix (QueueHandoff.focused body) w h).1 with
  | error stop=>trivial
  | ok out=>exact kept

theorem publication_borrow (items : List SkbId) : Driver.ProductHistorySafe Good (Publication.borrow items) := by
  unfold Publication.borrow Admission.actualOps
  simp only [TxSource.observed,TxSource.Ops.focus]
  cases items.head? with
  | none=>exact focused Good extend _
  | some first=>
    repeat' first
      | (driver_history_head focusPrefix; exact focused Good extend _)
      | driver_product_history_step

theorem publication_middle (pid : PeerId) (first : SkbId) (state : PacketState) :
    Driver.ProductHistorySafe Good (Publication.middle pid first state) := by
  unfold Publication.middle Admission.actualOps
  simp only [TxSource.observed,TxSource.Ops.focus]
  repeat' first
    | (driver_history_head focusPrefix; exact focused Good extend _)
    | driver_product_history_step

theorem publication_good (items : List SkbId) (state : PacketState) (w : World) (before : Good h) :
    Good (runPrefix (TxSource.publish Admission.actualOps items state) w h).2 := by
  rw [Publication.factor,runPrefix_bind]
  obtain ⟨_,_,borrowGood,_⟩ := publication_borrow Good extend items w h before
  cases acquired : runPrefix (Publication.borrow items) w h with
  | mk outcome borrowHistory=>
    rw [acquired] at borrowGood
    cases outcome with
    | error stop=>exact borrowGood
    | ok out=>
      obtain ⟨⟨first,pid⟩,u⟩ := out
      simp only [runPrefix_bind]
      obtain ⟨_,_,middleGood,_⟩ := publication_middle Good extend pid first state u borrowHistory borrowGood
      cases published : runPrefix (Publication.middle pid first state) u borrowHistory with
      | mk result publishedHistory=>
        rw [published] at middleGood
        cases result with
        | error stop=>exact middleGood
        | ok out=>
          obtain ⟨ignored,v⟩ := out
          cases ignored
          have funded := Publication.observed_middle_funded pid first state
            (Publication.observed_borrow_funded items acquired) published
          obtain ⟨g,ambient,cutHistory,cut,returned,_,_⟩ := Publication.repayment_nonfinal pid funded publishedHistory
          simp only []
          rw [returned]
          obtain ⟨access,position⟩ := PeerRelease.cut_history (some pid) v.wg v.ambient publishedHistory
          rw [cut] at position
          change cutHistory=publishedHistory++_ at position
          have atCut : Good cutHistory := by
            rw [position]
            apply extend _ _ middleGood
            intro event member
            obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
            exact ⟨rfl,Source.peer_access_quiet original⟩
          apply extend _ _ atCut
          intro event member
          cases List.mem_singleton.mp member
          exact ⟨rfl,release_none_quiet rfl⟩

theorem publication (items : List SkbId) (state : PacketState) :
    Driver.ProductHistorySafe Good (TxSource.publish Admission.actualOps items state) := by
  intro w h before
  obtain ⟨suffix,extended⟩ := Admission.publication_appends items state w h
  have kept := publication_good Good extend items state w before
  refine ⟨suffix,extended,kept,?_⟩
  cases result : (runPrefix (TxSource.publish Admission.actualOps items state) w h).1 with
  | error stop=>trivial
  | ok out=>exact kept

theorem admission_history (pid : PeerId) (items : List SkbId) :
    Driver.ProductHistorySafe Good (Admission.actual pid items) := by
  unfold Admission.actual Admission.front
  repeat' first
    | (driver_history_head TxSource.publish; exact publication Good extend _ _)
    | (driver_history_head TxSource.Ops.step; exact focused Good extend _)
    | (driver_history_head TxSource.Ops.access; exact focused Good extend _)
    | (driver_history_head TxSource.Ops.enqueue; exact focused Good extend _)
    | driver_product_history_step

omit extend in
theorem quiet_growth (h : List CausalJournal.Event) :
    ∀ current suffix,
      (∃ prior,current=h++prior ∧ ∀ event∈prior,birthPackets event=[] ∧ Quiet event)→
      (∀ event∈suffix,birthPackets event=[] ∧ Quiet event)→
      ∃ grown,current++suffix=h++grown ∧ ∀ event∈grown,birthPackets event=[] ∧ Quiet event := by
  intro current suffix ⟨prior,same,old⟩ later
  exact ⟨prior++suffix,by simp [same,List.append_assoc],fun event member=>(List.mem_append.mp member).elim (old event) (later event)⟩

omit extend in
theorem admission_cuts (pid : PeerId) (items : List SkbId)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg) :
    ∃ suffix,(runPrefix (Admission.actual pid items) w h).2=h++suffix ∧ Cuts CompleteProduct.Safe h suffix := by
  obtain ⟨_,_,⟨suffix,same,quiet⟩,_⟩ := admission_history
    (fun current=>∃ prior,current=h++prior ∧ ∀ event∈prior,birthPackets event=[] ∧ Quiet event)
    (quiet_growth h) pid items w h ⟨[],by simp,by simp⟩
  exact ⟨suffix,same,CompletePrefix.quiet_cuts before
    (fun event member=>(quiet event member).1) (fun event member=>(quiet event member).2)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging.Creation
