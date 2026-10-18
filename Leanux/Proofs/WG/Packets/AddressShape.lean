import Leanux.Proofs.WG.AllowedIps.LookupExecution

/-! Packet address facts about the actual constructors and ECN rewrites.
Constructor destinations are stated as byte slices (including truncation of an
unbounded supplied Nat); wgXmit's separate equality guard identifies the Nat.
No mixed-family arbitrary packet-list premise is silently assumed. -/
namespace Leanux.Proofs.WG.Packets
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.AllowedIps

/- Select an exposed source head before applying a checked Hoare rule. -/
open Lean Meta Elab Tactic in
elab "packet_hoare_head " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 3 do throwError "not a Hoare contract"
  let action := args[args.size - 3]!.consumeMData.headBeta
  let expected ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless action.getAppFn.constName? == some expected do
    throwError "different packet action head"


open Lean Meta Elab Tactic in
elab "packet_bind_head " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 3 do throwError "not a Hoare contract"
  let action := args[args.size - 3]!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let bindArgs := action.getAppArgs
  unless bindArgs.size ≥ 2 do throwError "missing bind action"
  let first := bindArgs[bindArgs.size - 2]!.consumeMData.headBeta
  let expected ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless first.getAppFn.constName? == some expected do
    throwError "different first packet action"


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
  simp [List.append_assoc, hp, beBytes_length]

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

  apply (hoare_iff_run _ _ _).mpr
  intro w packet v _ hr
  by_cases ht : tos > 255
  · simp [Env.xmitPacket, ht, invariant, AmbientM.invariant] at hr
    cases hr
  · by_cases h4 : family = 4
    · subst family
      simp only [Env.xmitPacket, ht, ite_false, ite_true, Nat.reduceBEq,
        StateT.run_pure] at hr
      rcases hr with ⟨rfl, rfl⟩
      unfold DestinationShape
      apply Or.inl
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp only [List.append_assoc, List.cons_append, List.nil_append, List.headD_cons]
        decide
      · simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]
        omega
      · apply destination_slice
        simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]
    · by_cases h6 : family = 6
      · subst family
        simp only [Env.xmitPacket, ht, ite_false, ite_true, Nat.reduceBEq] at hr
        rcases hr with ⟨rfl, rfl⟩
        unfold DestinationShape
        apply Or.inr
        refine ⟨rfl, ?_, ?_, ?_⟩
        · simp only [List.append_assoc, List.cons_append, List.nil_append, List.headD_cons, UInt8.toNat_ofNat']
          omega
        · simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]
          omega
        · apply destination_slice
          simp only [List.length_append, List.length_cons, List.length_nil, beBytes_length]
      · simp [Env.xmitPacket, ht, h4, h6, unsupported, AmbientM.unsupported] at hr
        cases hr

theorem xmitPackets_shape (family addr : Nat) (payload : List UInt8) (opts : XmitOpts) :
    ⦃fun _ => ⌜True⌝⦄ Env.xmitPackets family addr payload opts
    ⦃⇓? result _ => ⌜∀ packets mtu, result = .ok (packets, mtu) →
      ∀ packet ∈ packets, DestinationShape family addr packet.bytes⌝⦄ := by

  let Q := fun (result : Except Int (List Packet × Nat)) (_ : World) =>
    ∀ packets mtu, result = .ok (packets, mtu) →
      ∀ packet ∈ packets, DestinationShape family addr packet.bytes
  have single (mtu : Nat) : Hoare (do
      let packet ← Env.xmitPacket family addr payload mtu opts.tos
      pure (Except.ok ([packet], mtu))) (fun _ : World => True) Q := by
    refine hoare_bind _ _ (xmitPacket_shape family addr payload mtu opts.tos) ?_
    intro packet
    apply hoare_consequence (hoare_pure (.ok ([packet], mtu) : Except Int (List Packet × Nat)) _)
      (fun _ h => h)
    intro result w h
    rcases h with ⟨rfl, hp⟩
    intro packets actualMtu hr x hx
    cases hr
    simpa only [List.mem_singleton.mp hx] using hp
  have hd : Hoare (MonadLift.monadLift getDev : Leanux.M Device) (fun _ => True) (fun _ _ => True) :=
    (hoare_iff_run _ _ _).mpr (fun _ _ _ _ _ => trivial)
  have he : Hoare getEnv (fun _ : World => True) (fun _ _ => True) :=
    (hoare_iff_run _ _ _).mpr (fun _ _ _ _ _ => trivial)
  have stop (msg : String) : Hoare (unsupported msg : Leanux.M (Except Int (List Packet × Nat)))
      (fun _ => True) Q := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v _ hr
    simp [unsupported, AmbientM.unsupported] at hr
    cases hr

  have abort {α : Type} (msg : String) (f : α → Leanux.M (Except Int (List Packet × Nat))) :
      Hoare (unsupported msg >>= f) (fun _ => True) Q := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v _ hr
    simp [unsupported, AmbientM.unsupported] at hr
    cases hr
  have conditional (p : Prop) [Decidable p] (a b : Leanux.M (Except Int (List Packet × Nat)))
      (ha : p → Hoare a (fun _ => True) Q) (hb : ¬p → Hoare b (fun _ => True) Q) :
      Hoare (if p then a else b) (fun _ => True) Q := by
    by_cases hp : p
    · simpa only [ite_eq_left hp] using ha hp
    · simpa only [ite_eq_right hp] using hb hp
  change Hoare _ (fun _ => True) Q
  unfold Env.xmitPackets
  refine hoare_bind _ _ hd ?_
  intro dev
  refine hoare_bind _ _ he ?_
  intro env
  dsimp only
  cases opts.gsoSize <;> simp only
  all_goals repeat' first
    | (packet_bind_head Env.xmitPacket; exact single _)
    | (packet_bind_head Leanux.unsupported; exact abort _ _)
    | (packet_hoare_head Leanux.unsupported; exact stop _)
    | (packet_hoare_head Pure.pure
       apply hoare_consequence (hoare_pure _ _) (fun _ h => h)
       intro result w h
       rcases h with ⟨rfl, _⟩
       intro packets mtu hr packet hp
       cases hr
       all_goals simp_all [Q, List.mem_map]
       all_goals obtain ⟨i, _, rfl⟩ := hp
       all_goals exact gsoSegment_shape _ _ _ _)
    | (packet_hoare_head ite; apply conditional; all_goals intro h)
    | simp only

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
    | cons b bs => simp [List.take]
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
    | cons b bs => simp [List.take]
  · change beAt _ 8 16 = beAt bytes 8 16
    rw [beAt_prefix _ _ 8 16 (by omega), hp]
    simp [beAt, List.drop_drop]

private theorem addressPreserved_refl (v4 : Bool) (bytes : List UInt8) :
    AddressPreserved v4 bytes bytes := ⟨rfl, rfl, rfl⟩

private theorem ipEcnSetCe_address (bytes : List UInt8) (hl : 20 ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ ipEcnSetCe bytes
    ⦃⇓? out _ => ⌜AddressPreserved true bytes out⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient out v ambient' _ hr
  simp only [ipEcnSetCe, branch, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    Leanux.Proofs.WG.CounterWindow.branch_run, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
    StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure] at hr
  split at hr <;> simp only [StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure,
    Except.ok.injEq, Prod.mk.injEq] at hr
  all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals first
    | exact addressPreserved_refl _ _
    | exact rewrite4_address bytes _ _ _ hl

private theorem ipEcnSetEct1_address (bytes : List UInt8) (hl : 20 ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ ipEcnSetEct1 bytes
    ⦃⇓? out _ => ⌜AddressPreserved true bytes out⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient out v ambient' _ hr
  simp only [ipEcnSetEct1, branch, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    Leanux.Proofs.WG.CounterWindow.branch_run, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
    StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure] at hr
  split at hr <;> simp only [StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure,
    Except.ok.injEq, Prod.mk.injEq] at hr
  all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals first
    | exact addressPreserved_refl _ _
    | exact rewrite4_address bytes _ _ _ hl

private theorem ip6EcnSetCe_address (bytes : List UInt8) (hl : 40 ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ ip6EcnSetCe bytes
    ⦃⇓? out _ => ⌜AddressPreserved false bytes out⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient out v ambient' _ hr
  simp only [ip6EcnSetCe, branch, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    Leanux.Proofs.WG.CounterWindow.branch_run, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
    StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure] at hr
  split at hr <;> simp only [StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure,
    Except.ok.injEq, Prod.mk.injEq] at hr
  all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals first
    | exact addressPreserved_refl _ _
    | exact rewrite6_address bytes _ hl

private theorem ip6EcnSetEct1_address (bytes : List UInt8) (hl : 40 ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ ip6EcnSetEct1 bytes
    ⦃⇓? out _ => ⌜AddressPreserved false bytes out⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient out v ambient' _ hr
  simp only [ip6EcnSetEct1, branch, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    Leanux.Proofs.WG.CounterWindow.branch_run, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
    StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure] at hr
  split at hr <;> simp only [StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure,
    Except.ok.injEq, Prod.mk.injEq] at hr
  all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals first
    | exact addressPreserved_refl _ _
    | exact rewrite6_address bytes _ hl

theorem inetEcnSet_address (ce v4 : Bool) (bytes : List UInt8)
    (hl : (if v4 then 20 else 40) ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ inetEcnSet ce (if v4 then 4 else 6) bytes
    ⦃⇓? out _ => ⌜AddressPreserved v4 bytes out⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient out v ambient' _ hr
  cases v4 with
  | false =>
    have h40 : ¬bytes.length < 40 := by simpa using (Nat.not_lt.mpr hl)
    cases ce <;> simp [inetEcnSet, branch, AmbientM.branch, h40] at hr
    · exact (hoare_iff_run_ambient _ _ _).mp (ip6EcnSetEct1_address bytes hl) _ _ _ _ _ trivial hr
    · exact (hoare_iff_run_ambient _ _ _).mp (ip6EcnSetCe_address bytes hl) _ _ _ _ _ trivial hr
  | true =>
    have h20 : ¬bytes.length < 20 := by simpa using (Nat.not_lt.mpr hl)
    cases ce <;> simp [inetEcnSet, branch, AmbientM.branch, h20] at hr
    · exact (hoare_iff_run_ambient _ _ _).mp (ipEcnSetEct1_address bytes hl) _ _ _ _ _ trivial hr
    · exact (hoare_iff_run_ambient _ _ _).mp (ipEcnSetCe_address bytes hl) _ _ _ _ _ trivial hr

theorem inetEcnDecapsulate_address (v4 : Bool) (outer : Nat) (bytes : List UInt8)
    (hl : (if v4 then 20 else 40) ≤ bytes.length) :
    ⦃fun _ => ⌜True⌝⦄ inetEcnDecapsulate (if v4 then 4 else 6) outer bytes
    ⦃⇓? out _ => ⌜AddressPreserved v4 bytes out⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient out v ambient' _ hr
  have hs := fun ce => (hoare_iff_run_ambient _ _ _).mp (inetEcnSet_address ce v4 bytes hl)
  cases v4
  all_goals simp only [inetEcnDecapsulate, Bool.false_eq_true, ite_false, ite_true] at hr hs
  all_goals repeat' first
    | (exact hs _ _ _ _ _ _ trivial hr)
    | (rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩; exact addressPreserved_refl _ _)
    | (simp only [branch, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        Leanux.Proofs.WG.CounterWindow.branch_run, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
        StateT.run_pure, Leanux.Proofs.WG.CounterWindow.except_pure,
        Bool.false_eq_true, ite_false] at hr)
    | split at hr

theorem sourceAddress_take (v4 : Bool) (bytes : List UInt8) (len : Nat)
    (hl : (if v4 then 20 else 40) ≤ len) :
    sourceAddress v4 (bytes.take len) = sourceAddress v4 bytes := by
  cases v4 <;> simp only [sourceAddress, Bool.false_eq_true, ↓reduceIte] at *
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
  all_goals simp only [List.length_take, hh, hhead, Bool.false_eq_true, ite_false, ite_true] at *
  all_goals try (split at hp <;> simp_all)
  all_goals try (split at hp <;> simp_all)
  all_goals omega

end Leanux.Proofs.WG.Packets
