import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionNestedLoop

/-! Pipe disposal uses its native ring-size test and increments the actual
loop index. Ring-size preservation of buffer release supplies the decreasing
measure; suspended records are tracked independently. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

def pipeRing (pid : PipeId) (s : FSWorld) : Nat :=
  ((s.pipes[pid]?).map (·.ringSize)).getD 0

theorem pipe_of (f : File) : Keeps (pipeOf f) := by
  nested_suspension_source [pipeOf] using [invariant]

theorem pipe_buffer (pid : PipeId) (i : Nat) : Keeps (getPipeBuf pid i) := by
  nested_suspension_source [getPipeBuf] using [get_pipe,invariant]

theorem pipe_buffer_set (pid : PipeId) (i : Nat) (b : PipeBuffer) : Keeps (setPipeBuf pid i b) := by
  nested_suspension_source [setPipeBuf] using [get_pipe,set_pipe,invariant]

theorem pipe_page_put (page : PageId) : Keeps (putPipePage page) := by
  nested_suspension_source [putPipePage] using [get_page,set_page,invariant]

theorem pipe_buffer_anon_release (pid : PipeId) (buf : PipeBuffer) : Keeps (anonPipeBufRelease pid buf) := by
  nested_suspension_source [anonPipeBufRelease] using
    [get_pipe,set_pipe,get_page,branch,compare,invariant,pipe_page_put]

theorem pipe_buffer_release (pid : PipeId) (i : Nat) : Keeps (pipeBufRelease pid i) := by
  nested_suspension_source [pipeBufRelease] using
    [pipe_buffer,pipe_buffer_set,invariant,pipe_buffer_anon_release]

theorem fs_branch_preserves (P : FSWorld→Prop) (d : Decision) (b : Bool) :
    Preserves P (Leanux.branch d b : FS.M Bool) := by
  apply (fs_hoare_iff _ _ _).mpr
  intro s t a r v u c before run
  cases run
  exact before

theorem fs_compare_preserves (P : FSWorld→Prop) (d : Decision) (b : Bool) (x y : Int) :
    Preserves P (branchCmp d b x y : FS.M Bool) := by
  apply (fs_hoare_iff _ _ _).mpr
  intro s t a r v u c before run
  cases run
  exact before

theorem fs_invariant (P : FSWorld→Prop) (message : String) :
    Preserves P (Leanux.invariant message : FS.M α) := by
  apply (fs_hoare_iff _ _ _).mpr
  intro s t a r v u c before run
  cases run

theorem fs_pipe_read (P : FSWorld→Prop) (pid : PipeId) : Preserves P (getPipe pid) := by
  unfold getPipe
  repeat' first
    | (rx_retention_head MonadState.get
       exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    | (rx_retention_head Leanux.invariant; exact fs_invariant _ _)
    | routing_tx_step

theorem fs_page_read (P : FSWorld→Prop) (id : PageId) : Preserves P (getPage id) := by
  unfold getPage
  repeat' first
    | (rx_retention_head MonadState.get
       exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    | (rx_retention_head Leanux.invariant; exact fs_invariant _ _)
    | routing_tx_step

macro "pipe_ring_step" : tactic => `(tactic| first
  | (rx_retention_head getPipe; exact fs_pipe_read _ _)
  | (rx_retention_head getPage; exact fs_page_read _ _)
  | (rx_retention_head Leanux.branch; exact fs_branch_preserves _ _ _)
  | (rx_retention_head branchCmp; exact fs_compare_preserves _ _ _ _ _)
  | (rx_retention_head Leanux.invariant; exact fs_invariant _ _)
  | (rx_retention_head setPage; unfold setPage)
  | (rx_retention_head _root_.modify; apply hoare_modify; intro s h; exact h)
  | routing_tx_step)

theorem pipe_page_put_ring (pid : PipeId) (page : PageId) :
    SameView (pipeRing pid) (putPipePage page) := by
  intro initial
  change Preserves (fun s=>pipeRing pid s=initial) _
  unfold putPipePage
  repeat' pipe_ring_step

theorem pipe_cache_ring (pid : PipeId) (page : PageId) :
    SameView (pipeRing pid) (do setPipe pid {(←getPipe pid) with tmpPage:=some page}) := by
  intro initial
  apply (fs_hoare_iff _ _ _).mpr
  intro s t a result v u c before run
  cases hp:s.pipes[pid]? with
  | none=>simp [getPipe,setPipe,hp,Leanux.invariant,AmbientM.invariant] at run; cases run
  | some p=>
    simp [getPipe,setPipe,hp] at run
    obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩:=run
    simpa [pipeRing,hp] using before

theorem pipe_anon_release_ring (pid : PipeId) (buf : PipeBuffer) :
    SameView (pipeRing pid) (anonPipeBufRelease pid buf) := by
  intro initial
  change Preserves (fun s=>pipeRing pid s=initial) _
  unfold anonPipeBufRelease
  repeat' first
    | (rx_retention_head putPipePage; exact pipe_page_put_ring _ _ initial)
    | (run_tac
         let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
         let some raw := target.getAppArgs.back? | throwError "missing action"
         let action := raw.consumeMData.headBeta
         unless action.isAppOf ``Bind.bind do throwError "not a bind"
         let args:=action.getAppArgs
         let some first:=args[args.size-2]? | throwError "missing first action"
         unless first.consumeMData.headBeta.isAppOf ``getPipe do throwError "not a pipe update"
         let some next:=args.back? | throwError "missing continuation"
         Lean.Meta.lambdaTelescope next fun _ body=>do
           unless body.consumeMData.headBeta.isAppOf ``setPipe do throwError "not a pipe write"
       exact pipe_cache_ring pid _ initial)
    | pipe_ring_step

theorem pipe_buffer_set_ring (pid : PipeId) (i : Nat) (buf : PipeBuffer) :
    SameView (pipeRing pid) (setPipeBuf pid i buf) := by
  intro initial
  apply (fs_hoare_iff _ _ _).mpr
  intro s t a result v u c before run
  cases hp:s.pipes[pid]? with
  | none=>simp [setPipeBuf,getPipe,hp,Leanux.invariant,AmbientM.invariant] at run; cases run
  | some p=>
    simp [setPipeBuf,getPipe,setPipe,hp] at run
    split at run
    · simp at run
      obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩:=run
      simpa [pipeRing,hp] using before
    · cases run

theorem fs_pipe_buffer_read (P : FSWorld→Prop) (pid : PipeId) (i : Nat) :
    Preserves P (getPipeBuf pid i) := by
  unfold getPipeBuf
  repeat' pipe_ring_step

theorem pipe_buffer_release_ring (pid : PipeId) (i : Nat) :
    SameView (pipeRing pid) (pipeBufRelease pid i) := by
  intro initial
  change Preserves (fun s=>pipeRing pid s=initial) _
  unfold pipeBufRelease
  repeat' first
    | (rx_retention_head getPipeBuf; exact fs_pipe_buffer_read _ _ _)
    | (rx_retention_head setPipeBuf; exact pipe_buffer_set_ring _ _ _ initial)
    | (rx_retention_head anonPipeBufRelease; exact pipe_anon_release_ring _ _ initial)
    | pipe_ring_step

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
