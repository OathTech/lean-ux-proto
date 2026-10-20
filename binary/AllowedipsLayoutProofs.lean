import AllowedipsImage
import LayoutTactic

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Binary.AllowedipsLookup
local instance : Labels := Image.linkedLabels

theorem r00_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x00)
      AllowedipsImage.Lookup.r00 := by
  binary_layout

theorem r20_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x20)
      AllowedipsImage.Lookup.r20 := by
  binary_layout

theorem r3e_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x3e)
      AllowedipsImage.Lookup.r3e := by
  binary_layout

theorem r47_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x47)
      AllowedipsImage.Lookup.r47 := by
  binary_layout

theorem r4c_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x4c)
      AllowedipsImage.Lookup.r4c := by
  binary_layout

theorem r58_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x58)
      AllowedipsImage.Lookup.r58 := by
  binary_layout

theorem r61_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x61)
      AllowedipsImage.Lookup.r61 := by
  binary_layout

theorem r66_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x66)
      AllowedipsImage.Lookup.r66 := by
  binary_layout

theorem r74_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x74)
      AllowedipsImage.Lookup.r74 := by
  binary_layout

theorem r79_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x79)
      AllowedipsImage.Lookup.r79 := by
  binary_layout

theorem r87_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x87)
      AllowedipsImage.Lookup.r87 := by
  binary_layout

theorem r8c_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x8c)
      AllowedipsImage.Lookup.r8c := by
  binary_layout

theorem r90_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x90)
      AllowedipsImage.Lookup.r90 := by
  binary_layout

theorem r95_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x95)
      AllowedipsImage.Lookup.r95 := by
  binary_layout

theorem ra4_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0xa4)
      AllowedipsImage.Lookup.ra4 := by
  binary_layout

theorem raf_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0xaf)
      AllowedipsImage.Lookup.raf := by
  binary_layout

theorem rb4_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0xb4)
      AllowedipsImage.Lookup.rb4 := by
  binary_layout

theorem rb9_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0xb9)
      AllowedipsImage.Lookup.rb9 := by
  binary_layout

theorem rd5_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0xd5)
      AllowedipsImage.Lookup.rd5 := by
  binary_layout

theorem rda_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0xda)
      AllowedipsImage.Lookup.rda := by
  binary_layout

theorem rea_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0xea)
      AllowedipsImage.Lookup.rea := by
  binary_layout

theorem rfc_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0xfc)
      AllowedipsImage.Lookup.rfc := by
  binary_layout

theorem r101_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x101)
      AllowedipsImage.Lookup.r101 := by
  binary_layout

theorem r106_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x106)
      AllowedipsImage.Lookup.r106 := by
  binary_layout

theorem r10b_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x10b)
      AllowedipsImage.Lookup.r10b := by
  binary_layout

theorem r110_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x110)
      AllowedipsImage.Lookup.r110 := by
  binary_layout

theorem r119_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x119)
      AllowedipsImage.Lookup.r119 := by
  binary_layout

theorem r122_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x122)
      AllowedipsImage.Lookup.r122 := by
  binary_layout

theorem r12b_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x12b)
      AllowedipsImage.Lookup.r12b := by
  binary_layout

theorem r13c_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x13c)
      AllowedipsImage.Lookup.r13c := by
  binary_layout

theorem r14f_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x14f)
      AllowedipsImage.Lookup.r14f := by
  binary_layout

theorem r154_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x154)
      AllowedipsImage.Lookup.r154 := by
  binary_layout

theorem r171_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x171)
      AllowedipsImage.Lookup.r171 := by
  binary_layout

theorem r176_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x176)
      AllowedipsImage.Lookup.r176 := by
  binary_layout

theorem r184_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.Lookup.entry + 0x184)
      AllowedipsImage.Lookup.r184 := by
  binary_layout

#print axioms r00_layout
#print axioms r20_layout
#print axioms r3e_layout
#print axioms r47_layout
#print axioms r4c_layout
#print axioms r58_layout
#print axioms r61_layout
#print axioms r66_layout
#print axioms r74_layout
#print axioms r79_layout
#print axioms r87_layout
#print axioms r8c_layout
#print axioms r90_layout
#print axioms r95_layout
#print axioms ra4_layout
#print axioms raf_layout
#print axioms rb4_layout
#print axioms rb9_layout
#print axioms rd5_layout
#print axioms rda_layout
#print axioms rea_layout
#print axioms rfc_layout
#print axioms r101_layout
#print axioms r106_layout
#print axioms r10b_layout
#print axioms r110_layout
#print axioms r119_layout
#print axioms r122_layout
#print axioms r12b_layout
#print axioms r13c_layout
#print axioms r14f_layout
#print axioms r154_layout
#print axioms r171_layout
#print axioms r176_layout
#print axioms r184_layout
end Binary.AllowedipsLookup
