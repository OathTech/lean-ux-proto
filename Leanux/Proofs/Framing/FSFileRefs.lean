import Leanux.Proofs.Framing.WGKernel
import Leanux.FS.File

/-! Shared strong frames for the original file-reference helpers. Each body
is proved here once; narrower lifetime views use projection corollaries.
The fput frame ends when fput returns, before any queued task work executes. -/
namespace Leanux.Proofs.Framing.FSFileRefs
open Leanux Std.Do

theorem getFile_sameWGKernel (id : FileId) : SameWGKernel (getFile id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getFile, getK, invariant]
  all_goals simp_all

theorem getFile_spec (P : WGKernelView → Prop) (id : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ getFile id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (getFile_sameWGKernel id).wp P

theorem setFile_sameWGKernel (id : FileId) (f : File) : SameWGKernel (setFile id f) := by
  intro w x w' hr
  cases hr
  rfl

theorem setFile_spec (P : WGKernelView → Prop) (id : FileId) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ setFile id f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (setFile_sameWGKernel id f).wp P

theorem freeFile_sameWGKernel (id : FileId) : SameWGKernel (freeFile id) := by
  intro w x w' hr
  cases hr
  rfl

theorem freeFile_spec (P : WGKernelView → Prop) (id : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ freeFile id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (freeFile_sameWGKernel id).wp P

theorem fileFree_sameWGKernel (fid : FileId) : SameWGKernel (fileFree fid) := by
  apply SameView.of_wp
  intro s
  have get_spec := getFile_spec (fun v => v = s)
  have free_spec := freeFile_spec (fun v => v = s)
  mvcgen [fileFree, get_spec, free_spec, branchCmp, branch, modifyK, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [wgKernelView, WGKernelView.ofKernel]

theorem fileFree_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ fileFree fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (fileFree_sameWGKernel fid).wp P

theorem fput_sameWGKernel (fid : FileId) : SameWGKernel (fput fid) := by
  apply SameView.of_wp
  intro s
  have get_spec := getFile_spec (fun v => v = s)
  have set_spec := setFile_spec (fun v => v = s)
  have free_spec := fileFree_spec (fun v => v = s)
  mvcgen [fput, get_spec, set_spec, free_spec, getK, modifyK, branch, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [wgKernelView, WGKernelView.ofKernel]

theorem fput_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ fput fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (fput_sameWGKernel fid).wp P

theorem fdput_sameWGKernel (f : Fd) : SameWGKernel (fdput f) := by
  apply SameView.of_wp
  intro s
  have put_spec := fput_spec (fun v => v = s)
  mvcgen [fdput, put_spec, branch]
  all_goals simp_all

theorem fdput_spec (P : WGKernelView → Prop) (f : Fd) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ fdput f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (fdput_sameWGKernel f).wp P

end Leanux.Proofs.Framing.FSFileRefs
