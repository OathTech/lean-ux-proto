import AllowedipsImage
import LayoutTactic

set_option maxRecDepth 4096
namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

theorem r00_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x00)
      AllowedipsImage.CommonBits.r00 := by
  binary_layout

theorem r15_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x15)
      AllowedipsImage.CommonBits.r15 := by
  binary_layout

theorem r21_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x21)
      AllowedipsImage.CommonBits.r21 := by
  binary_layout

theorem r26_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x26)
      AllowedipsImage.CommonBits.r26 := by
  binary_layout

theorem r2b_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x2b)
      AllowedipsImage.CommonBits.r2b := by
  binary_layout

theorem r39_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x39)
      AllowedipsImage.CommonBits.r39 := by
  binary_layout

theorem r3e_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x3e)
      AllowedipsImage.CommonBits.r3e := by
  binary_layout

theorem r43_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x43)
      AllowedipsImage.CommonBits.r43 := by
  binary_layout

theorem r4c_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x4c)
      AllowedipsImage.CommonBits.r4c := by
  binary_layout

theorem r51_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x51)
      AllowedipsImage.CommonBits.r51 := by
  binary_layout

theorem r6c_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x6c)
      AllowedipsImage.CommonBits.r6c := by
  binary_layout

theorem r75_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x75)
      AllowedipsImage.CommonBits.r75 := by
  binary_layout

theorem r7a_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x7a)
      AllowedipsImage.CommonBits.r7a := by
  binary_layout

theorem r8e_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x8e)
      AllowedipsImage.CommonBits.r8e := by
  binary_layout

theorem r93_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x93)
      AllowedipsImage.CommonBits.r93 := by
  binary_layout

theorem r98_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x98)
      AllowedipsImage.CommonBits.r98 := by
  binary_layout

theorem raa_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xaa)
      AllowedipsImage.CommonBits.raa := by
  binary_layout

theorem raf_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xaf)
      AllowedipsImage.CommonBits.raf := by
  binary_layout

theorem rb9_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xb9)
      AllowedipsImage.CommonBits.rb9 := by
  binary_layout

theorem rc4_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xc4)
      AllowedipsImage.CommonBits.rc4 := by
  binary_layout

theorem rc9_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0xc9)
      AllowedipsImage.CommonBits.rc9 := by
  binary_layout

end Binary.CommonBits
