import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSocket
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionAccounting

/-! Post-socket byte accounting preserves the same semantic ledger and
cleanup debts. On Stop, the frontier stores the actual accounting entry and
failed source run after the first-terminal socket receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity StagedProvenance Queues.RxCredits CompletionCuts

theorem entry_view_of_parts
    (material : PacketOrigins.snapshot v = PacketOrigins.snapshot w)
    (queues : Staged.stagedAt v = Staged.stagedAt w)
    (shape : StagingOccurrences.geometry v = StagingOccurrences.geometry w)
    (owner : ownershipPointView v = ownershipPointView w) :
    StagedEntry.view v = StagedEntry.view w := by
  have handoff : handoffTxView v = handoffTxView w := by
    funext pid
    have fields := congrArg (Option.map (fun p : PeerOwnership => p.2.1))
      (congrFun (congrArg (fun x => x.2.2.1) owner) pid)
    simpa only [ownershipPointView,ownershipAt,handoffTxView,peerOwnership,peerAt,
      Option.map_map,Function.comp_def] using fields
  have owners := queueContents_of_exact handoff
  obtain ⟨epoch,cells⟩ := Prod.mk.inj material
  obtain ⟨snapshot,packets⟩ := Prod.mk.inj shape
  change Packets.epoch v = Packets.epoch w at epoch
  simp only [StagedEntry.view,epoch,queues,cells,snapshot,packets,owners]

private theorem accounting_frame (view : WGWorld → σ)
    (peerFrame : SameView view (do
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + packet.value.bytes.length})) :
    SameView (fun w : World => view w.wg) (FirstTerminal.accountingNative pid packet ret) := by
  have branchFrame : SameView view (branch .sendSkbOk (ret == 0) : WG.M Bool) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    rfl
  have lift_frame {α} (action : WG.M α) (frame : SameView view action) :=
    sameView_liftWG (fun w : World => view w.wg) view action frame (fun _ _ _ same => same)
  intro initial
  unfold FirstTerminal.accountingNative
  apply preserves_bind (lift_frame _ branchFrame initial)
  intro sent
  cases sent
  · exact preserves_pure _
  · exact preserves_bind (lift_frame _ peerFrame initial) (fun _ => preserves_pure _)

theorem accounting_entry_view (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) :
    SameView (fun w : World => StagedEntry.view w.wg) (FirstTerminal.accountingNative pid packet ret) := by
  have staged := accounting_frame (pid := pid) (packet := packet) (ret := ret) Staged.stagedAt
    (Staged.Exact.update_peer pid _ (fun _ => ⟨rfl,rfl⟩))
  have geometry : SameView StagingOccurrences.geometry (do
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + packet.value.bytes.length}) := by
    intro initial
    change Preserves (fun w => StagingOccurrences.geometry w = initial) _
    repeat' staging_geometry_step initial
  have shape := accounting_frame (pid := pid) (packet := packet) (ret := ret) _ geometry
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v native
  exact entry_view_of_parts
    ((ProjectedAction.iff_run _ _ _).mp (FirstTerminal.accounting_snapshot pid packet ret) w value v native)
    ((ProjectedAction.iff_run _ _ _).mp staged w value v native)
    ((ProjectedAction.iff_run _ _ _).mp shape w value v native)
    ((ProjectedAction.iff_run _ _ _).mp (accounting_ownership pid packet ret) w value v native)

structure IndexedFrontier (context : Context) (ledger : Staged.Obligations.Ledger) (debts : List CleanupDebt)
    (reason : Stop) (history : List CausalJournal.Event) where
  phase : Phase
  site : Site
  world : World
  before : List CausalJournal.Event
  owned : Owned context phase before ledger debts world
  prefixHistory : before.IsPrefix history
  nativeFailure : runPrefix site.action world before = (.error reason,history)
  lastCut : history.filterMap ledgerEvent? = before.filterMap ledgerEvent?
  sameBirths : births history = births before

def IndexedStopped (context : Context) (ledger : Staged.Obligations.Ledger) (debts : List CleanupDebt)
    (reason : Stop) (history : List CausalJournal.Event) : Prop :=
  Nonempty (IndexedFrontier context ledger debts reason history)

theorem indexed_passive_checked (site : Site) (source : site.action = discard action)
    (appends : Appends action) (quiet : HistoryFrame ledgerEvent? action)
    (birthFrame : ∀ w history suffix, (runPrefix action w history).2 = history ++ suffix →
      ∀ event ∈ suffix, birthPackets event = [])
    (erases : ErasesPrefix action native)
    (frame : SameView (fun w : World => StagedEntry.view w.wg) native) :
    Ensures (fun h w => Owned context phase h ledger debts w)
      (IndexedStopped context ledger debts) action
      (fun _ h w => Owned context phase h ledger debts w) := by
  intro w history before
  obtain ⟨suffix,grown⟩ := appends w history
  have quietSuffix := birthFrame w history suffix grown
  refine ⟨suffix,grown,?_⟩
  cases run : runPrefix action w history with
  | mk result after =>
    cases result with
    | error reason =>
      refine ⟨⟨phase,site,w,history,before,?_,?_,?_,?_⟩⟩
      · exact ⟨suffix,by simpa only [run] using grown.symm⟩
      · rw [source,discard,runPrefix_bind,run]
      · simpa only [run] using quiet w history
      · have same : births (runPrefix action w history).2 = births history := by
          rw [grown]
          exact births_quiet_suffix history suffix quietSuffix
        simpa only [run] using same
    | ok result =>
      obtain ⟨value,v⟩ := result
      have nativeRun := (erases w history).symm.trans (congrArg Prod.fst run)
      have kept := before.same_view ((ProjectedAction.iff_run _ _ _).mp frame w value v nativeRun)
      simp only [run] at grown
      simpa only [grown] using kept.append suffix quietSuffix

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
