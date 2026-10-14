import Image
import RegionExecution
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Binary.Image
local instance : Labels := linkedLabels
theorem PeerGet_r00_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 0) PeerGet.r00 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r12_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 18) PeerGet.r12 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r1b_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 27) PeerGet.r1b := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r20_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 32) PeerGet.r20 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r2d_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 45) PeerGet.r2d := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r32_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 50) PeerGet.r32 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r3b_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 59) PeerGet.r3b := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r3f_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 63) PeerGet.r3f := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r44_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 68) PeerGet.r44 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r60_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 96) PeerGet.r60 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r69_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 105) PeerGet.r69 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r6e_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 110) PeerGet.r6e := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r77_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 119) PeerGet.r77 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r7b_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 123) PeerGet.r7b := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r80_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 128) PeerGet.r80 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r8a_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 138) PeerGet.r8a := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r8f_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 143) PeerGet.r8f := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r94_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 148) PeerGet.r94 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_r9d_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 157) PeerGet.r9d := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_ra2_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 162) PeerGet.ra2 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rb0_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 176) PeerGet.rb0 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rb5_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 181) PeerGet.rb5 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rbe_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 190) PeerGet.rbe := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rc3_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 195) PeerGet.rc3 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rcf_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 207) PeerGet.rcf := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rd4_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 212) PeerGet.rd4 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rdd_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 221) PeerGet.rdd := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_re1_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 225) PeerGet.re1 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_re6_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 230) PeerGet.re6 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rf0_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 240) PeerGet.rf0 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem PeerGet_rf2_layout :
    LaidOut fetch (PeerGet.entry + .ofNat 242) PeerGet.rf2 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r00_layout :
    LaidOut fetch (Lookup.entry + .ofNat 0) Lookup.r00 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r19_layout :
    LaidOut fetch (Lookup.entry + .ofNat 25) Lookup.r19 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r34_layout :
    LaidOut fetch (Lookup.entry + .ofNat 52) Lookup.r34 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r39_layout :
    LaidOut fetch (Lookup.entry + .ofNat 57) Lookup.r39 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r42_layout :
    LaidOut fetch (Lookup.entry + .ofNat 66) Lookup.r42 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r47_layout :
    LaidOut fetch (Lookup.entry + .ofNat 71) Lookup.r47 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r4c_layout :
    LaidOut fetch (Lookup.entry + .ofNat 76) Lookup.r4c := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r59_layout :
    LaidOut fetch (Lookup.entry + .ofNat 89) Lookup.r59 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r5e_layout :
    LaidOut fetch (Lookup.entry + .ofNat 94) Lookup.r5e := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r63_layout :
    LaidOut fetch (Lookup.entry + .ofNat 99) Lookup.r63 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r6c_layout :
    LaidOut fetch (Lookup.entry + .ofNat 108) Lookup.r6c := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r71_layout :
    LaidOut fetch (Lookup.entry + .ofNat 113) Lookup.r71 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r73_layout :
    LaidOut fetch (Lookup.entry + .ofNat 115) Lookup.r73 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r78_layout :
    LaidOut fetch (Lookup.entry + .ofNat 120) Lookup.r78 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r89_layout :
    LaidOut fetch (Lookup.entry + .ofNat 137) Lookup.r89 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r95_layout :
    LaidOut fetch (Lookup.entry + .ofNat 149) Lookup.r95 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_r9a_layout :
    LaidOut fetch (Lookup.entry + .ofNat 154) Lookup.r9a := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_ra8_layout :
    LaidOut fetch (Lookup.entry + .ofNat 168) Lookup.ra8 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_rad_layout :
    LaidOut fetch (Lookup.entry + .ofNat 173) Lookup.rad := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_rb2_layout :
    LaidOut fetch (Lookup.entry + .ofNat 178) Lookup.rb2 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_rba_layout :
    LaidOut fetch (Lookup.entry + .ofNat 186) Lookup.rba := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_rc5_layout :
    LaidOut fetch (Lookup.entry + .ofNat 197) Lookup.rc5 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
theorem Lookup_rca_layout :
    LaidOut fetch (Lookup.entry + .ofNat 202) Lookup.rca := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl
end Binary.Image
