import AllowedipsImage
import RegionExecution

set_option maxRecDepth 4096
namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

theorem r00_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x00)
      AllowedipsImage.CommonBits.r00 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r15_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x15)
      AllowedipsImage.CommonBits.r15 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r21_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x21)
      AllowedipsImage.CommonBits.r21 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r26_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x26)
      AllowedipsImage.CommonBits.r26 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r2b_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x2b)
      AllowedipsImage.CommonBits.r2b := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r39_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x39)
      AllowedipsImage.CommonBits.r39 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r3e_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x3e)
      AllowedipsImage.CommonBits.r3e := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r43_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x43)
      AllowedipsImage.CommonBits.r43 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r4c_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x4c)
      AllowedipsImage.CommonBits.r4c := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r51_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x51)
      AllowedipsImage.CommonBits.r51 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r6c_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x6c)
      AllowedipsImage.CommonBits.r6c := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r75_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x75)
      AllowedipsImage.CommonBits.r75 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r7a_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x7a)
      AllowedipsImage.CommonBits.r7a := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r8e_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x8e)
      AllowedipsImage.CommonBits.r8e := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r93_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x93)
      AllowedipsImage.CommonBits.r93 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem r98_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x98)
      AllowedipsImage.CommonBits.r98 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem raa_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xaa)
      AllowedipsImage.CommonBits.raa := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem raf_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xaf)
      AllowedipsImage.CommonBits.raf := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem rb9_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xb9)
      AllowedipsImage.CommonBits.rb9 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem rc4_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xc4)
      AllowedipsImage.CommonBits.rc4 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

theorem rc9_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xc9)
      AllowedipsImage.CommonBits.rc9 := by
  repeat first
    | apply LaidOut.cons
    | exact LaidOut.nil _
    | apply regular_mono
    | exact True.intro
    | decide
    | rfl

end Binary.CommonBits
