import Leanux.Proofs.Framing.SeccompBridge
import Leanux.Proofs.Framing.Control

/-! Frames for each original checker and translator over its actual M instance. -/
namespace Leanux.Proofs.Framing.SeccompFrames
open Leanux Std.Do Leanux.Seccomp
set_option maxHeartbeats 3000000
set_option pp.structureInstances false

theorem chkCodeAllowed_sameWGKernel (code : UInt16) : SameWGKernel (chkCodeAllowed (m := M) code) := by
  frame_wg [chkCodeAllowed] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec, cmpGe_spec]

theorem chkCodeAllowed_spec (P : WGKernelView → Prop) (code : UInt16) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ chkCodeAllowed (m := M) code
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (chkCodeAllowed_sameWGKernel code).wp P

theorem checkLoadAndStores_sameWGKernel (filter : Leanux.Seccomp.ClassicProg) : SameWGKernel (checkLoadAndStores (m := M) filter) := by
  frame_wg [checkLoadAndStores] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec]

theorem checkLoadAndStores_spec (P : WGKernelView → Prop) (filter : Leanux.Seccomp.ClassicProg) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ checkLoadAndStores (m := M) filter
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (checkLoadAndStores_sameWGKernel filter).wp P

theorem bpfCheckClassic_sameWGKernel (filter : Leanux.Seccomp.ClassicProg) : SameWGKernel (bpfCheckClassic (m := M) filter) := by
  frame_wg [bpfCheckClassic] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec, cmpEq_spec, cmpGe_spec, chkCodeAllowed_spec, checkLoadAndStores_spec]

theorem bpfCheckClassic_spec (P : WGKernelView → Prop) (filter : Leanux.Seccomp.ClassicProg) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ bpfCheckClassic (m := M) filter
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (bpfCheckClassic_sameWGKernel filter).wp P

theorem bpfCheckBasicsOk_sameWGKernel (filter : Option Leanux.Seccomp.ClassicProg) (flen : Nat) : SameWGKernel (bpfCheckBasicsOk (m := M) filter flen) := by
  frame_wg [bpfCheckBasicsOk] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec]

theorem bpfCheckBasicsOk_spec (P : WGKernelView → Prop) (filter : Option Leanux.Seccomp.ClassicProg) (flen : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ bpfCheckBasicsOk (m := M) filter flen
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (bpfCheckBasicsOk_sameWGKernel filter flen).wp P

theorem seccompCheckFilter_sameWGKernel (filter : Leanux.Seccomp.ClassicProg) : SameWGKernel (seccompCheckFilter (m := M) filter) := by
  frame_wg [seccompCheckFilter] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec, cmpGe_spec, cmpFlag_spec]

theorem seccompCheckFilter_spec (P : WGKernelView → Prop) (filter : Leanux.Seccomp.ClassicProg) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ seccompCheckFilter (m := M) filter
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (seccompCheckFilter_sameWGKernel filter).wp P

theorem emitJmp_sameWGKernel (site : EmitSite) (target : Int) (len : Nat) (addrs : Option (Array Nat))
    (i emitted : Nat) : SameWGKernel (emitJmp (m := M) site target len addrs i emitted) := by
  frame_wg [emitJmp] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec, cmpLt_spec, cmpGe_spec]

theorem emitJmp_spec (P : WGKernelView → Prop) (site : EmitSite) (target : Int) (len : Nat) (addrs : Option (Array Nat))
    (i emitted : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ emitJmp (m := M) site target len addrs i emitted
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (emitJmp_sameWGKernel site target len addrs i emitted).wp P

theorem bpfConvertFilter_sameWGKernel (prog : Leanux.Seccomp.ClassicProg) (newProg : Option Nat) (seenLdAbsIn : Bool)
    (newLenIn : Nat) : SameWGKernel (bpfConvertFilter (m := M) prog newProg seenLdAbsIn newLenIn) := by
  unfold bpfConvertFilter
  repeat' first
    | (view_head SeccompM.branch; exact sbranch_sameWGKernel _ _)
    | (view_head SeccompM.branchCmp; exact sbranchCmp_sameWGKernel _ _ _ _)
    | (view_head SeccompM.alloc; exact salloc_sameWGKernel _)
    | (view_head SeccompM.invariant; exact sinvariant_sameWGKernel _)
    | (view_head cmpEq; exact cmpEq_sameWGKernel _ _ _)
    | (view_head cmpNe; exact cmpNe_sameWGKernel _ _ _)
    | (view_head cmpLt; exact cmpLt_sameWGKernel _ _ _)
    | (view_head cmpGt; exact cmpGt_sameWGKernel _ _ _)
    | (view_head emitJmp; exact emitJmp_sameWGKernel _ _ _ _ _ _)
    | view_step
  apply view_loop _ _ (fun b => (3 - b.2.2.2.2).toNat)
  · intro b
    repeat' first
      | (view_head SeccompM.branch; exact sbranch_sameWGKernel _ _)
      | (view_head SeccompM.branchCmp; exact sbranchCmp_sameWGKernel _ _ _ _)
      | (view_head SeccompM.alloc; exact salloc_sameWGKernel _)
      | (view_head SeccompM.invariant; exact sinvariant_sameWGKernel _)
      | (view_head cmpEq; exact cmpEq_sameWGKernel _ _ _)
      | (view_head cmpNe; exact cmpNe_sameWGKernel _ _ _)
      | (view_head cmpLt; exact cmpLt_sameWGKernel _ _ _)
      | (view_head cmpGt; exact cmpGt_sameWGKernel _ _ _)
      | (view_head emitJmp; exact emitJmp_sameWGKernel _ _ _ _ _ _)
      | view_step
  · intro b
    have branch_spec := sbranch_spec (fun _ => True)
    have cmp_spec := sbranchCmp_spec (fun _ => True)
    have eq_spec := cmpEq_spec (fun _ => True)
    have ne_spec := cmpNe_spec (fun _ => True)
    have lt_spec := cmpLt_spec (fun _ => True)
    have emit_spec := emitJmp_spec (fun _ => True)
    have inv_spec := @sinvariant_spec (fun _ => True)
    have any_range {β : Type} (r : Std.Legacy.Range) (init : β) (f : Nat → β → M (ForInStep β)) :
        ⦃⌜True⌝⦄ forIn r init f ⦃⇓? _ _ => ⌜True⌝⦄ := by
      apply (hoare_iff_triple _ _ _).mp
      intro w x w' hw hr
      trivial
    mvcgen [-Std.Do.Spec.forIn_range, -Std.Do.Spec.forIn'_range, branch_spec, cmp_spec, eq_spec, ne_spec, lt_spec, emit_spec, inv_spec, cmpGt_result, any_range]
    all_goals try exact ((⇓? _ _ => ⌜True⌝) : PostCond _ (.arg World (.except Stop .pure)))
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
    all_goals omega

theorem bpfConvertFilter_spec (P : WGKernelView → Prop) (prog : Leanux.Seccomp.ClassicProg) (newProg : Option Nat) (seenLdAbsIn : Bool)
    (newLenIn : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ bpfConvertFilter (m := M) prog newProg seenLdAbsIn newLenIn
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (bpfConvertFilter_sameWGKernel prog newProg seenLdAbsIn newLenIn).wp P

theorem checkTranslatedRecords_sameWGKernel (insns : Array Leanux.Seccomp.BpfInsn) : SameWGKernel (checkTranslatedRecords (m := M) insns) := by
  frame_wg [checkTranslatedRecords] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec]

theorem checkTranslatedRecords_spec (P : WGKernelView → Prop) (insns : Array Leanux.Seccomp.BpfInsn) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ checkTranslatedRecords (m := M) insns
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (checkTranslatedRecords_sameWGKernel insns).wp P

theorem bpfMigrateFilter_sameWGKernel (insns : Leanux.Seccomp.ClassicProg) (orig : Leanux.Seccomp.ClassicProg) : SameWGKernel (bpfMigrateFilter (m := M) insns orig) := by
  frame_wg [bpfMigrateFilter] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec, bpfConvertFilter_spec, checkTranslatedRecords_spec]

theorem bpfMigrateFilter_spec (P : WGKernelView → Prop) (insns : Leanux.Seccomp.ClassicProg) (orig : Leanux.Seccomp.ClassicProg) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ bpfMigrateFilter (m := M) insns orig
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (bpfMigrateFilter_sameWGKernel insns orig).wp P

theorem bpfPrepareFilter_sameWGKernel (insns : Leanux.Seccomp.ClassicProg) (orig : Leanux.Seccomp.ClassicProg) : SameWGKernel (bpfPrepareFilter (m := M) insns orig) := by
  frame_wg [bpfPrepareFilter] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec, bpfCheckClassic_spec, bpfMigrateFilter_spec, seccompCheckFilter_spec]

theorem bpfPrepareFilter_spec (P : WGKernelView → Prop) (insns : Leanux.Seccomp.ClassicProg) (orig : Leanux.Seccomp.ClassicProg) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ bpfPrepareFilter (m := M) insns orig
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (bpfPrepareFilter_sameWGKernel insns orig).wp P

theorem bpfProgStoreOrigFilter_sameWGKernel  : SameWGKernel (bpfProgStoreOrigFilter (m := M) ) := by
  frame_wg [bpfProgStoreOrigFilter] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec]

theorem bpfProgStoreOrigFilter_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ bpfProgStoreOrigFilter (m := M)
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (bpfProgStoreOrigFilter_sameWGKernel ).wp P

theorem bpfProgAlloc_sameWGKernel  : SameWGKernel (bpfProgAlloc (m := M) ) := by
  frame_wg [bpfProgAlloc] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec]

theorem bpfProgAlloc_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ bpfProgAlloc (m := M)
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (bpfProgAlloc_sameWGKernel ).wp P

theorem bpfProgCreateFromUser_sameWGKernel (fprog : SockFprog) : SameWGKernel (bpfProgCreateFromUser (m := M) fprog) := by
  frame_wg [bpfProgCreateFromUser] using [sbranch_spec, sbranchCmp_spec, salloc_spec, stranslatedInsn_spec, stranslatedLen_spec, srecordMismatch_spec, sunsupported_spec, sinvariant_spec, bpfCheckBasicsOk_spec, bpfPrepareFilter_spec, bpfProgStoreOrigFilter_spec, bpfProgAlloc_spec]

theorem bpfProgCreateFromUser_spec (P : WGKernelView → Prop) (fprog : SockFprog) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ bpfProgCreateFromUser (m := M) fprog
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (bpfProgCreateFromUser_sameWGKernel fprog).wp P

end Leanux.Proofs.Framing.SeccompFrames
