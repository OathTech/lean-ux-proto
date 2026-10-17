import Leanux.Proofs.WG.Noise.StateEdges

set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- A prefix may be forgotten only when the suffix establishes its own
postcondition. This lemma deliberately promises no state preservation. -/
theorem unconstrained_prefix {σ α : Type} (a : StateT σ (Except Stop) α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  intro _ _ _ _ _
  trivial

theorem consumeResponse_tag (msg : List UInt8) :
    Ensures (consumeResponse msg) (fun _ => True)
      (fun result w => ∀ pid, result = some pid →
        tagAt w pid = some HANDSHAKE_CONSUMED_RESPONSE) := by
  let P : WGWorld → Prop := fun _ => True
  let R : Option PeerId → WGWorld → Prop := fun result g => ∀ pid, result = some pid →
    tagAt g pid = some HANDSHAKE_CONSUMED_RESPONSE
  have hany {α : Type} (a : WG.M α) : Ensures a P (fun _ => P) := by
    intro _ _ _ _ _ _ _
    trivial
  have hnone : Ensures (pure none : WG.M (Option PeerId)) P R := by
    intro g ambient x g' ambient' hp hr
    cases hr
    intro pid impossible
    cases impossible
  have hstop (what : String) : Ensures (invariant what : WG.M (Option PeerId)) P R := by
    intro g ambient x g' ambient' hp hr
    simp [invariant, AmbientM.invariant] at hr
    cases hr
  have hfail (pid : PeerId) : Ensures (do peerPut (some pid); pure none) P R :=
    ensures_bind _ _ (hany _) (fun _ => hnone)
  have hfinish (pid : PeerId) (f : Peer → Peer)
      (tag : ∀ p, (f p).handshakeState = HANDSHAKE_CONSUMED_RESPONSE) :
      Ensures (do setPeer pid (f (← getPeer pid)); pure (some pid)) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient result g' ambient' hp hr
    change Except.ok ((some pid, {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid (f p)})}), ambient) = _ at hr
    cases hr
    intro target same
    cases same
    cases hd : g.dev with
    | none => simp [peerAt, hd] at hp
    | some d => simp [tagAt, peerAt, tag]
  change Ensures _ P R
  unfold consumeResponse
  refine ensures_bind _ _ (hany _) ?_
  intro d
  refine ensures_bind _ _ (hany _) ?_
  intro noIdentity
  cases noIdentity with
  | true => exact hnone
  | false =>
    refine ensures_bind _ _ (hany _) ?_
    intro entry
    refine ensures_bind _ _ (hany _) ?_
    intro missing
    cases missing with
    | true => exact hnone
    | false =>
      cases entry with
      | none => exact hstop _
      | some entry =>
        rcases entry with ⟨owner, pid⟩
        cases owner with
        | keypair _ => exact hstop _
        | handshake owner =>
          refine ensures_bind _ _ (hany _) ?_
          intro p
          refine ensures_bind _ _ (hany _) ?_
          intro wrongState
          cases wrongState with
          | true => exact hfail pid
          | false =>
            refine ensures_bind _ _ (hany _) ?_
            intro ephemeral
            rcases ephemeral with ⟨ck, hash⟩
            refine ensures_bind _ _ (hany _) ?_
            intro ee
            refine ensures_bind _ _ (hany _) ?_
            intro eeFailed
            cases eeFailed with
            | true => exact hfail pid
            | false =>
              cases ee with
              | none => exact hstop _
              | some ee =>
                rcases ee with ⟨ck, key⟩
                refine ensures_bind _ _ (hany _) ?_
                intro se
                refine ensures_bind _ _ (hany _) ?_
                intro seFailed
                cases seFailed with
                | true => exact hfail pid
                | false =>
                  cases se with
                  | none => exact hstop _
                  | some se =>
                    rcases se with ⟨ck, key⟩
                    refine ensures_bind _ _ (hany _) ?_
                    intro outs
                    refine ensures_bind _ _ (hany _) ?_
                    intro ck
                    refine ensures_bind _ _ (hany _) ?_
                    intro tempHash
                    refine ensures_bind _ _ (hany _) ?_
                    intro key
                    refine ensures_bind _ _ (hany _) ?_
                    intro dec
                    refine ensures_bind _ _ (hany _) ?_
                    intro decFailed
                    cases decFailed with
                    | true => exact hfail pid
                    | false =>
                      cases dec with
                      | none => exact hstop _
                      | some decrypted =>
                        rcases decrypted with ⟨plain, hash⟩
                        refine ensures_bind _ _ (hany _) ?_
                        intro nowPeer
                        refine ensures_bind _ _ (hany _) ?_
                        intro changed
                        cases changed with
                        | true => exact hfail pid
                        | false => exact hfinish pid _ (fun _ => rfl)

theorem consumeInitiation_tag (msg : List UInt8) :
    Ensures (consumeInitiation msg) (fun _ => True)
      (fun result w => ∀ pid, result = some pid →
        tagAt w pid = some HANDSHAKE_CONSUMED_INITIATION) := by
  let P : WGWorld → Prop := fun _ => True
  let R : Option PeerId → WGWorld → Prop := fun result g => ∀ pid, result = some pid →
    tagAt g pid = some HANDSHAKE_CONSUMED_INITIATION
  let out (peer ret : Option PeerId) : WG.M (Option PeerId) := do
    if ← branch .consumeFailedPut ret.isNone then peerPut peer
    pure ret
  have hany {α : Type} (a : WG.M α) : Ensures a P (fun _ => P) := by
    intro _ _ _ _ _ _ _
    trivial
  have hnone (peer : Option PeerId) : Ensures (out peer none) P R := by
    unfold out
    refine ensures_bind _ _ (hany _) ?_
    intro b
    cases b
    · intro g ambient x g' ambient' hp hr
      cases hr
      intro pid impossible
      cases impossible
    · refine ensures_bind _ _ (hany _) ?_
      intro _ g ambient x g' ambient' hp hr
      cases hr
      intro pid impossible
      cases impossible
  have hstop (what : String) : Ensures (invariant what : WG.M (Option PeerId)) P R := by
    intro g ambient x g' ambient' hp hr
    simp [invariant, AmbientM.invariant] at hr
    cases hr
  have hfinish (pid : PeerId) :
      Ensures (do
        setPeer pid {(← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION}
        out (some pid) (some pid)) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient result g' ambient' hp hr
    simp [setPeer, modifyDev, out, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    intro target same
    cases same
    cases hd : g.dev with
    | none => simp [peerAt, hd] at hp
    | some d => simp [tagAt, peerAt]
  change Ensures _ P R
  unfold consumeInitiation
  refine ensures_bind _ _ (hany _) ?_
  intro d
  refine ensures_bind _ _ (hany _) ?_
  intro noIdentity
  cases noIdentity with
  | true => exact hnone none
  | false =>
    refine ensures_bind _ _ (hany _) ?_
    intro ephemeral
    rcases ephemeral with ⟨ck, hash⟩
    refine ensures_bind _ _ (hany _) ?_
    intro es
    refine ensures_bind _ _ (hany _) ?_
    intro esFailed
    cases esFailed with
    | true => exact hnone none
    | false =>
      cases es with
      | none => exact hstop _
      | some es =>
        rcases es with ⟨ck, key⟩
        refine ensures_bind _ _ (hany _) ?_
        intro st
        refine ensures_bind _ _ (hany _) ?_
        intro staticFailed
        cases staticFailed with
        | true => exact hnone none
        | false =>
          cases st with
          | none => exact hstop _
          | some st =>
            rcases st with ⟨s, hash⟩
            refine ensures_bind _ _ (hany _) ?_
            intro peer
            refine ensures_bind _ _ (hany _) ?_
            intro noPeer
            cases noPeer with
            | true => exact hnone none
            | false =>
              cases peer with
              | none => exact hstop _
              | some pid =>
                refine ensures_bind _ _ (hany _) ?_
                intro peerState
                refine ensures_bind _ _ (hany _) ?_
                intro ss
                refine ensures_bind _ _ (hany _) ?_
                intro ssFailed
                cases ssFailed with
                | true => exact hnone (some pid)
                | false =>
                  cases ss with
                  | none => exact hstop _
                  | some ss =>
                    rcases ss with ⟨ckSs, key⟩
                    refine ensures_bind _ _ (hany _) ?_
                    intro ts
                    refine ensures_bind _ _ (hany _) ?_
                    intro timestampFailed
                    cases timestampFailed with
                    | true => exact hnone (some pid)
                    | false =>
                      cases ts with
                      | none => exact hstop _
                      | some ts =>
                        rcases ts with ⟨t, hashT⟩
                        refine ensures_bind _ _ (hany _) ?_
                        intro p
                        refine ensures_bind _ _ (hany _) ?_
                        intro now
                        refine ensures_bind _ _ (hany _) ?_
                        intro replayOrFlood
                        cases replayOrFlood with
                        | true => exact hnone (some pid)
                        | false =>
                          rw [← bind_assoc]
                          refine ensures_bind _ _ (hany _) ?_
                          intro _
                          refine ensures_bind _ _ (hany _) ?_
                          intro newer
                          have htail : Ensures (do
                              setPeer pid {(← getPeer pid) with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4}
                              let consumption ← hiddenClock64 .consumptionNow
                              let last := (← getPeer pid).lastInitiationConsumption
                              let diff : Int64 := last - consumption
                              if ← branchCmp .consumeLaterTime (diff < 0) diff.toInt 0 then
                                setPeer pid {(← getPeer pid) with lastInitiationConsumption := consumption}
                              setPeer pid {(← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION}
                              out (some pid) (some pid)) P R := by
                            rw [← bind_assoc]
                            refine ensures_bind _ _ (hany _) ?_
                            intro _
                            refine ensures_bind _ _ (hany _) ?_
                            intro consumption
                            refine ensures_bind _ _ (hany _) ?_
                            intro lastPeer
                            refine ensures_bind _ _ (hany _) ?_
                            intro later
                            cases later with
                            | false => exact hfinish pid
                            | true =>
                              refine ensures_bind _ _ (hany _) ?_
                              intro _
                              refine ensures_bind _ _ (hany _) ?_
                              intro _
                              exact hfinish pid
                          cases newer with
                          | false => exact htail
                          | true =>
                            refine ensures_bind _ _ (hany _) ?_
                            intro _
                            refine ensures_bind _ _ (hany _) ?_
                            intro _
                            exact htail

end Leanux.Proofs.WG.Noise
