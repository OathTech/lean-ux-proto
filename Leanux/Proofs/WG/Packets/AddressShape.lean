import Leanux.Proofs.WG.AllowedIps.LookupExecution

/-! Packet address facts about the actual constructors and ECN rewrites.
Constructor destinations are stated as byte slices (including truncation of an
unbounded supplied Nat); wgXmit's separate equality guard identifies the Nat.
No mixed-family arbitrary packet-list premise is silently assumed. -/
namespace Leanux.Proofs.WG.Packets
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.AllowedIps

theorem beBytes_length (addr width : Nat) : (Env.beBytes addr width).length = width := by
  simp [Env.beBytes]

def DestinationShape (family addr : Nat) (bytes : List UInt8) : Prop :=
  (family = 4 ∧ (bytes.headD 0).toNat / 16 = 4 ∧ 20 ≤ bytes.length ∧
    (bytes.drop 16).take 4 = Env.beBytes addr 4) ∨
  (family = 6 ∧ (bytes.headD 0).toNat / 16 = 6 ∧ 40 ≤ bytes.length ∧
    (bytes.drop 24).take 16 = Env.beBytes addr 16)

theorem destination_slice (pre post : List UInt8) (addr off width : Nat)
    (hp : pre.length = off) :
    (((pre ++ Env.beBytes addr width) ++ post).drop off).take width = Env.beBytes addr width := by
  simp [List.append_assoc, List.drop_append, hp, List.take_append, beBytes_length]

theorem gsoSegment_shape (addr index : Nat) (slice : List UInt8) (mtu : Nat) :
    DestinationShape 4 addr (Env.gsoSegment addr index slice mtu).bytes := by
  unfold Env.gsoSegment DestinationShape
  dsimp only
  apply Or.inl
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [List.append_assoc, List.cons_append, List.nil_append, List.headD_cons]
    decide
  · simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]
    omega
  · apply destination_slice
    simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]

theorem xmitPacket_shape (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) :
    ⦃fun _ => ⌜True⌝⦄ Env.xmitPacket family addr payload mtu tos
    ⦃⇓? packet _ => ⌜DestinationShape family addr packet.bytes⌝⦄ := by
  mvcgen [Env.xmitPacket, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all only [beq_iff_eq]
  all_goals unfold DestinationShape
  · apply Or.inl
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [List.append_assoc, List.cons_append, List.nil_append, List.headD_cons]
      decide
    · simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]
      omega
    · apply destination_slice
      simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]
  · apply Or.inr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [List.append_assoc, List.cons_append, List.nil_append, List.headD_cons, UInt8.toNat_ofNat']
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]
      omega
    · apply destination_slice
      simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]

theorem xmitPackets_shape (family addr : Nat) (payload : List UInt8) (opts : XmitOpts) :
    ⦃fun _ => ⌜True⌝⦄ Env.xmitPackets family addr payload opts
    ⦃⇓? result _ => ⌜∀ packets mtu, result = .ok (packets, mtu) →
      ∀ packet ∈ packets, DestinationShape family addr packet.bytes⌝⦄ := by
  have hs := fun mtu => xmitPacket_shape family addr payload mtu opts.tos
  mvcgen [Env.xmitPackets, getDev, getK, invariant, unsupported, hs]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [List.mem_map, gsoSegment_shape]

theorem rst4_shape (bytes : List UInt8) :
    DestinationShape 4 (WG.beAt bytes 12 4) (Stack.rst4 bytes) := by
  unfold Stack.rst4
  dsimp only
  split <;> dsimp only
  all_goals unfold DestinationShape
  all_goals apply Or.inl
  all_goals refine ⟨rfl, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [List.append_assoc, List.cons_append, List.nil_append, List.headD_cons]; decide)
    | (simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]; omega)
    | (apply destination_slice; simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length])

/-- Trimming after the entire address field cannot change that field. -/
theorem beAt_take (bytes : List UInt8) (off count len : Nat) (h : off + count ≤ len) :
    WG.beAt (bytes.take len) off count = WG.beAt bytes off count := by
  unfold WG.beAt
  rw [List.drop_take, List.take_take]
  congr 2
  omega

/-- Rewriting an earlier header prefix leaves a following address slice intact. -/
theorem beAt_prefix (pre tail : List UInt8) (off count : Nat) (h : pre.length ≤ off) :
    WG.beAt (pre ++ tail) off count = WG.beAt tail (off - pre.length) count := by
  simp only [WG.beAt, List.drop_append, List.drop_eq_nil_iff.mpr h, List.nil_append]

def AddressPreserved (v4 : Bool) (before after : List UInt8) : Prop :=
  after.length = before.length ∧ after.headD 0 = before.headD 0 ∧
    sourceAddress v4 after = sourceAddress v4 before

private theorem rewrite4_address (bytes : List UInt8) (tos c1 c2 : UInt8)
    (hl : 20 ≤ bytes.length) :
    AddressPreserved true bytes (bytes.take 1 ++ [tos] ++ (bytes.drop 2).take 8 ++ [c1, c2] ++ bytes.drop 12) := by
  have hp : (bytes.take 1 ++ [tos] ++ (bytes.drop 2).take 8 ++ [c1, c2]).length = 12 := by
    simp only [List.length_append, List.length_take, List.length_drop, List.length_cons, List.length_nil]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, hp, List.length_drop]
    omega
  · cases bytes with
    | nil => simp at hl
    | cons b bs => simp [List.take, List.append_assoc]
  · change beAt _ 12 4 = beAt bytes 12 4
    rw [beAt_prefix _ _ 12 4 (by omega), hp]
    simp [beAt]

private theorem rewrite6_address (bytes : List UInt8) (tos : UInt8)
    (hl : 40 ≤ bytes.length) :
    AddressPreserved false bytes (bytes.take 1 ++ [tos] ++ bytes.drop 2) := by
  have hp : (bytes.take 1 ++ [tos]).length = 2 := by
    simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, hp, List.length_drop]
    omega
  · cases bytes with
    | nil => simp at hl
    | cons b bs => simp [List.take, List.append_assoc]
  · change beAt _ 8 16 = beAt bytes 8 16
    rw [beAt_prefix _ _ 8 16 (by omega), hp]
    simp [beAt, List.drop_drop]

private theorem addressPreserved_refl (v4 : Bool) (bytes : List UInt8) :
    AddressPreserved v4 bytes bytes := ⟨rfl, rfl, rfl⟩

private theorem ipEcnSetCe_address (bytes : List UInt8) (hl : 20 ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ ipEcnSetCe bytes
    ⦃⇓? out _ => ⌜AddressPreserved true bytes out⌝⦄ := by
  mvcgen [ipEcnSetCe, branch]
  all_goals first | exact addressPreserved_refl _ _ | exact rewrite4_address bytes _ _ _ hl

private theorem ipEcnSetEct1_address (bytes : List UInt8) (hl : 20 ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ ipEcnSetEct1 bytes
    ⦃⇓? out _ => ⌜AddressPreserved true bytes out⌝⦄ := by
  mvcgen [ipEcnSetEct1, branch]
  all_goals first | exact addressPreserved_refl _ _ | exact rewrite4_address bytes _ _ _ hl

private theorem ip6EcnSetCe_address (bytes : List UInt8) (hl : 40 ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ ip6EcnSetCe bytes
    ⦃⇓? out _ => ⌜AddressPreserved false bytes out⌝⦄ := by
  mvcgen [ip6EcnSetCe, branch]
  all_goals first | exact addressPreserved_refl _ _ | exact rewrite6_address bytes _ hl

private theorem ip6EcnSetEct1_address (bytes : List UInt8) (hl : 40 ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ ip6EcnSetEct1 bytes
    ⦃⇓? out _ => ⌜AddressPreserved false bytes out⌝⦄ := by
  mvcgen [ip6EcnSetEct1, branch]
  all_goals first | exact addressPreserved_refl _ _ | exact rewrite6_address bytes _ hl

theorem inetEcnSet_address (ce v4 : Bool) (bytes : List UInt8)
    (hl : (if v4 then 20 else 40) ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ inetEcnSet ce (if v4 then 4 else 6) bytes
    ⦃⇓? out _ => ⌜AddressPreserved v4 bytes out⌝⦄ := by
  cases v4 with
  | false =>
    have ha := ip6EcnSetCe_address bytes hl
    have hb := ip6EcnSetEct1_address bytes hl
    cases ce <;> mvcgen [inetEcnSet, branch, invariant, ha, hb]
    all_goals simp_all
  | true =>
    have ha := ipEcnSetCe_address bytes hl
    have hb := ipEcnSetEct1_address bytes hl
    cases ce <;> mvcgen [inetEcnSet, branch, invariant, ha, hb]
    all_goals simp_all

theorem inetEcnDecapsulate_address (v4 : Bool) (outer : Nat) (bytes : List UInt8)
    (hl : (if v4 then 20 else 40) ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ inetEcnDecapsulate (if v4 then 4 else 6) outer bytes
    ⦃⇓? out _ => ⌜AddressPreserved v4 bytes out⌝⦄ := by
  have hs := fun ce => inetEcnSet_address ce v4 bytes hl
  mvcgen [inetEcnDecapsulate, hs, branch]
  all_goals exact addressPreserved_refl _ _

theorem sourceAddress_take (v4 : Bool) (bytes : List UInt8) (len : Nat)
    (hl : (if v4 then 20 else 40) ≤ len) :
    sourceAddress v4 (bytes.take len) = sourceAddress v4 bytes := by
  cases v4 <;> simp only [sourceAddress, Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at *
  · exact beAt_take bytes 8 16 len (by omega)
  · exact beAt_take bytes 12 4 len (by omega)

/-- ECN and a trim retaining the complete header preserve the actual parsed family. -/
theorem protocol_after_trim (v4 : Bool) (before after : List UInt8) (len : Nat)
    (hp : ipTunnelParseProtocol before = (if v4 then 4 else 6))
    (ha : AddressPreserved v4 before after) (hl : (if v4 then 20 else 40) ≤ len) :
    ipTunnelParseProtocol (after.take len) = (if v4 then 4 else 6) := by
  have hh : (after.take len).headD 0 = after.headD 0 := by
    cases len with
    | zero => cases v4 <;> simp at hl
    | succ n => cases after <;> rfl
  rcases ha with ⟨hlen, hhead, _⟩
  cases v4 <;> unfold ipTunnelParseProtocol at *
  all_goals simp only [List.length_take, hh, hhead, Bool.false_eq_true, Bool.true_eq, if_false, if_true] at *
  all_goals try (split at hp <;> simp_all)
  all_goals try (split at hp <;> simp_all)
  all_goals omega

end Leanux.Proofs.WG.Packets
