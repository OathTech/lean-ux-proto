import AllowedipsEntrySteps

namespace Binary.AllowedipsEntry
open TrustBase CommonBitsCoverage CommonBits
local instance : Labels := Image.linkedLabels

theorem before_family (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch) (cmpContract : AllowedipsTraceConstCmp1Contract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      AtPC initial coverage old ra (AllowedipsImage.Lookup.entry+0x3e) t.machine ∧
      Local (Writes initial coverage old) initial rxSection [] t) ⟨initial,[initial]⟩ := by
  have p := prologue fetch agree pre rxSection
  have a := chain_at fetch p (fun s state => pc_call fetch agree pcContract pre 0x1b (by simp) s state rxSection)
  have b := chain_at fetch (Q := AtPC initial coverage old ra (AllowedipsImage.Lookup.entry+0x39)) a (fun s state => initialize_query fetch agree pre s state rxSection)
  have d := chain_at fetch b (fun s state => cmp_call fetch agree cmpContract pre 0x39 (.inl rfl) s state rxSection)
  simpa only [List.nil_append,show AllowedipsImage.Lookup.entry+Int64.ofNat 0x39+5=AllowedipsImage.Lookup.entry+0x3e from rfl] using d

theorem path32 (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (family : c.bits=32)
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      QueryAtPC c initial coverage old ra (AllowedipsImage.Lookup.entry+0x61) t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x3e⟩ rxSection
        [decisionView rxSection .swapEndian32 true] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x3e⟩,[⟨s,AllowedipsImage.Lookup.entry+0x3e⟩]⟩ := by
  have first := family32 fetch agree pre s state rxSection
  simp only [family,↓reduceIte,show (32==32)=true from rfl] at first
  have second := chain_at fetch first (fun s state => pc_call fetch agree pcContract pre 0x171 (by simp) s state rxSection)
  have third := chain_at fetch (Q := QueryAtPC c initial coverage old ra (AllowedipsImage.Lookup.entry+0x61)) second (fun s state => endian32 fetch agree pre family s state rxSection)
  simpa only [List.append_nil] using third

theorem path128 (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch) (cmpContract : AllowedipsTraceConstCmp1Contract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (family : c.bits=128)
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      QueryAtPC c initial coverage old ra (AllowedipsImage.Lookup.entry+0x61) t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x3e⟩ rxSection
        [decisionView rxSection .swapEndian32 false,decisionView rxSection .swapEndian128 true] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x3e⟩,[⟨s,AllowedipsImage.Lookup.entry+0x3e⟩]⟩ := by
  have first := family32 fetch agree pre s state rxSection
  simp only [family,show ¬(128=32) by decide,↓reduceIte,show (128==32)=false from rfl] at first
  have second := chain_at fetch first (fun s state => pc_call fetch agree pcContract pre 0x47 (by simp) s state rxSection)
  have third := chain_at fetch second (fun s state => arguments128 fetch agree s state rxSection)
  have fourth := chain_at fetch third (fun s state => cmp_call fetch agree cmpContract pre 0x53 (.inr rfl) s state rxSection)
  have fifth := chain_at fetch fourth (fun s state => family128 fetch agree pre family s state rxSection)
  have sixth := chain_at fetch fifth (fun s state => pc_call fetch agree pcContract pre 0x14f (by simp) s state rxSection)
  have seventh := chain_at fetch (Q := QueryAtPC c initial coverage old ra (AllowedipsImage.Lookup.entry+0x61)) sixth (fun s state => endian128 fetch agree pre family s state rxSection)
  simpa only [List.append_nil,List.cons_append,List.nil_append] using seventh

def signature (bits rx : Nat) : List EventView :=
  if bits=32 then [decisionView rx .swapEndian32 true]
  else [decisionView rx .swapEndian32 false,decisionView rx .swapEndian128 true]

theorem query_entry (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch) (cmpContract : AllowedipsTraceConstCmp1Contract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      QueryAtPC c initial coverage old ra (AllowedipsImage.Lookup.entry+0x61) t.machine ∧
      Local (Writes initial coverage old) initial rxSection (signature c.bits rxSection) t)
      ⟨initial,[initial]⟩ := by
  have first := before_family fetch agree pcContract cmpContract pre rxSection
  have next : ∀ s, At initial coverage old ra s →
      Eventually (historyStep fetch) (fun t =>
        QueryAtPC c initial coverage old ra (AllowedipsImage.Lookup.entry+0x61) t.machine ∧
        Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x3e⟩ rxSection (signature c.bits rxSection) t)
        ⟨⟨s,AllowedipsImage.Lookup.entry+0x3e⟩,[⟨s,AllowedipsImage.Lookup.entry+0x3e⟩]⟩ := by
    intro s state
    obtain ⟨_,_,physical⟩ := pre.related.2.1
    rcases physical.1.1 with family | family
    · simpa only [signature,family,↓reduceIte] using path32 fetch agree pcContract pre family s state rxSection
    · simpa only [signature,family,show ¬(128=32) by decide,↓reduceIte] using path128 fetch agree pcContract cmpContract pre family s state rxSection
  simpa only [List.nil_append] using chain_at fetch first next

#print axioms query_entry
end Binary.AllowedipsEntry
