import C1BelowSplitTarget
import RegionExecution

/- Origin: trial source binary-trials/t1/Setup.lean (copied in t5) on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-!
Stage 3, setup for the direct arm: the layout of the segment's three regions under any `fetch`
that agrees with the generated image, at the addresses the target names. These are the landed
layout theorems of `AllowedipsMutationCodeLayout` (proved there by `binary_layout`), transported
by `LaidOut.agreement`; with `Binary.region_eventually` each turns an execution of a region's
directives into `Eventually (instructionStep fetch)`. Nothing here executes an instruction.
-/

namespace Binary.SplitStage3
open AllowedipsMutationImage TrustBase
local instance : Labels := Image.linkedLabels

/-- `+ 0x338 .. + 0x35a`: eight instructions. -/
theorem r338_layout {fetch : Int64 → Option Decoded} (mutation : AllowedipsMutationDecoderAgreement fetch) :
    LaidOut fetch (Add.entry + 0x338) Add.r338 := Add_r338_layout.agreement mutation.add

/-- `+ 0x35a .. + 0x373`: eight instructions. -/
theorem r35a_layout {fetch : Int64 → Option Decoded} (mutation : AllowedipsMutationDecoderAgreement fetch) :
    LaidOut fetch (Add.entry + 0x35a) Add.r35a := Add_r35a_layout.agreement mutation.add

/-- `+ 0x373 .. + 0x38c`: six instructions, the last the branch to `+ 0x6c0`. -/
theorem r373_layout {fetch : Int64 → Option Decoded} (mutation : AllowedipsMutationDecoderAgreement fetch) :
    LaidOut fetch (Add.entry + 0x373) Add.r373 := Add_r373_layout.agreement mutation.add

#print axioms r338_layout
#print axioms r35a_layout
#print axioms r373_layout

end Binary.SplitStage3
