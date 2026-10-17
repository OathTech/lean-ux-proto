import Leanux.Proofs.WG.Index.ConsumeFrames
import Leanux.Proofs.WG.Index.SendSource
import Leanux.WG.Receive

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem consumeInitiation_tables (msg : List UInt8) : Ensures (consumeInitiation msg)
    TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hread (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hstop {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
  have hset (pid : PeerId) (p : Peer) : Ensures (setPeer pid p) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (setPeer_tables pid p)
  have hput (pid : Option PeerId) : Ensures (peerPut pid) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (peerPut_tables pid)
  have hpub (key : Key) : Ensures (pubkeyLookup key) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (pubkeyLookup_tables key)
  have hephemeral (copy : Bool) (e ck hash : List UInt8) :
      Ensures (messageEphemeral copy e ck hash) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (messageEphemeral_wg_spec TablesSafeWG copy e ck hash)
  have hdh (key : Bool) (ck priv pub : List UInt8) :
      Ensures (mixDh key ck priv pub) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (mixDh_wg_spec TablesSafeWG key ck priv pub)
  have hpre (ck precomputed : List UInt8) :
      Ensures (mixPrecomputedDh ck precomputed) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (mixPrecomputedDh_wg_spec TablesSafeWG ck precomputed)
  have hdecrypt (sealed key hash : List UInt8) :
      Ensures (messageDecrypt sealed key hash) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (messageDecrypt_wg_spec TablesSafeWG sealed key hash)
  let out (peer ret : Option PeerId) : WG.M (Option PeerId) := do
    if ← branch .consumeFailedPut ret.isNone then peerPut peer
    pure ret
  have houtPeer (peer ret : Option PeerId) :
      Ensures (out peer ret) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold out
    refine ensures_bind _ _ (hbranch .consumeFailedPut _) ?_
    intro failed
    cases failed with
    | true => exact ensures_bind _ _ (hput peer) (fun _ => hpure ret)
    | false => exact hpure ret
  have hcheck (replay : Bool) (lhs now : Int64) :
      Ensures (WG.orM (branch .consumeReplay replay)
        (branchCmp .consumeFlood (lhs > now) lhs.toInt now.toInt))
        TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold WG.orM
    refine ensures_bind _ _ (hbranch .consumeReplay replay) ?_
    intro replayed
    cases replayed with
    | true => exact hpure true
    | false => exact hcmp .consumeFlood _ _ _
  unfold consumeInitiation
  refine ensures_bind _ _ hdev ?_
  intro d
  refine ensures_bind _ _ (hbranch .consumeNoIdentity _) ?_
  intro missing
  cases missing with
  | true => exact houtPeer none none
  | false =>
    refine ensures_bind _ _ (hephemeral true _ _ _) ?_
    rintro ⟨ck, hash⟩
    refine ensures_bind _ _ (hdh true _ _ _) ?_
    intro es
    refine ensures_bind _ _ (hbranch .consumeEsFailed _) ?_
    intro esFailed
    cases esFailed with
    | true => exact houtPeer none none
    | false =>
      cases es with
      | none => exact hstop _
      | some pair =>
        obtain ⟨ck, key⟩ := pair
        refine ensures_bind _ _ (hdecrypt _ _ _) ?_
        intro st
        refine ensures_bind _ _ (hbranch .consumeStaticFailed _) ?_
        intro stFailed
        cases stFailed with
        | true => exact houtPeer none none
        | false =>
          cases st with
          | none => exact hstop _
          | some pair =>
            obtain ⟨static, hash⟩ := pair
            refine ensures_bind _ _ (hpub static) ?_
            intro peer
            refine ensures_bind _ _ (hbranch .consumeNoPeer _) ?_
            intro noPeer
            cases noPeer with
            | true => exact houtPeer none none
            | false =>
              cases peer with
              | none => exact hstop _
              | some pid =>
                refine ensures_bind _ _ (hread pid) ?_
                intro precomputed
                refine ensures_bind _ _ (hpre _ _) ?_
                intro ss
                refine ensures_bind _ _ (hbranch .consumeSsFailed _) ?_
                intro ssFailed
                cases ssFailed with
                | true => exact houtPeer (some pid) none
                | false =>
                  cases ss with
                  | none => exact hstop _
                  | some pair =>
                    obtain ⟨ckSs, key⟩ := pair
                    refine ensures_bind _ _ (hdecrypt _ _ _) ?_
                    intro ts
                    refine ensures_bind _ _ (hbranch .consumeTimestampFailed _) ?_
                    intro tsFailed
                    cases tsFailed with
                    | true => exact houtPeer (some pid) none
                    | false =>
                      cases ts with
                      | none => exact hstop _
                      | some pair =>
                        obtain ⟨t, hashT⟩ := pair
                        refine ensures_bind _ _ (hread pid) ?_
                        intro p
                        refine ensures_bind _ _ (hambient (AmbientM.hiddenClock64 .floodNow)) ?_
                        intro now
                        refine ensures_bind _ _ (hcheck _ _ _) ?_
                        intro rejected
                        cases rejected with
                        | true => exact houtPeer (some pid) none
                        | false =>
                          refine ensures_bind _ _ (hread pid) ?_
                          intro current
                          refine ensures_bind _ _ (hset pid _) ?_
                          intro _
                          refine ensures_bind _ _ (hbranch .consumeNewerTimestamp _) ?_
                          intro newer
                          have htail : Ensures (do
                              setPeer pid { (← getPeer pid) with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4 }
                              let consumption ← hiddenClock64 .consumptionNow
                              let last := (← getPeer pid).lastInitiationConsumption
                              let diff : Int64 := last - consumption
                              if ← branchCmp .consumeLaterTime (diff < 0) diff.toInt 0 then
                                setPeer pid { (← getPeer pid) with lastInitiationConsumption := consumption }
                              setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
                              out (some pid) (some pid)) TablesSafeWG (fun _ => TablesSafeWG) := by
                            refine ensures_bind _ _ (hread pid) ?_
                            intro current
                            refine ensures_bind _ _ (hset pid _) ?_
                            intro _
                            refine ensures_bind _ _ (hambient (AmbientM.hiddenClock64 .consumptionNow)) ?_
                            intro consumption
                            refine ensures_bind _ _ (hread pid) ?_
                            intro current
                            refine ensures_bind _ _ (hcmp .consumeLaterTime _ _ _) ?_
                            intro later
                            have hfinish : Ensures (do
                                setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
                                out (some pid) (some pid)) TablesSafeWG (fun _ => TablesSafeWG) := by
                              refine ensures_bind _ _ (hread pid) ?_
                              intro current
                              refine ensures_bind _ _ (hset pid _) ?_
                              intro _
                              exact houtPeer (some pid) (some pid)
                            cases later with
                            | false => exact hfinish
                            | true =>
                              refine ensures_bind _ _ (hread pid) ?_
                              intro current
                              refine ensures_bind _ _ (hset pid _) ?_
                              intro _
                              exact hfinish
                          cases newer with
                          | false => exact htail
                          | true =>
                            refine ensures_bind _ _ (hread pid) ?_
                            intro current
                            refine ensures_bind _ _ (hset pid _) ?_
                            intro _
                            exact htail

theorem consumeResponse_tables (msg : List UInt8) : Ensures (consumeResponse msg)
    TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hread (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hstop {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
  have hset (pid : PeerId) (p : Peer) : Ensures (setPeer pid p) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (setPeer_tables pid p)
  have hput (pid : Option PeerId) : Ensures (peerPut pid) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (peerPut_tables pid)
  have hlookup (kinds : List IndexKind) (index : Nat) :
      Ensures (indexLookup kinds index) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (indexLookup_tables kinds index)
  have hephemeral (copy : Bool) (e ck hash : List UInt8) :
      Ensures (messageEphemeral copy e ck hash) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (messageEphemeral_wg_spec TablesSafeWG copy e ck hash)
  have hdh (key : Bool) (ck priv pub : List UInt8) :
      Ensures (mixDh key ck priv pub) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (mixDh_wg_spec TablesSafeWG key ck priv pub)
  have hdecrypt (sealed key hash : List UInt8) :
      Ensures (messageDecrypt sealed key hash) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (messageDecrypt_wg_spec TablesSafeWG sealed key hash)
  have hkdf (second third : Bool) (ck data : List UInt8) :
      Ensures (kdf second third ck data) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (kdf_wg_spec TablesSafeWG second third ck data)
  have hout (outs : List (List UInt8)) (i : Nat) :
      Ensures (kdfOut outs i) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (kdfOut_wg_spec TablesSafeWG outs i)
  unfold consumeResponse
  refine ensures_bind _ _ hdev ?_
  intro d
  refine ensures_bind _ _ (hbranch .crespNoIdentity _) ?_
  intro absent
  cases absent with
  | true => exact hpure none
  | false =>
    refine ensures_bind _ _ (hlookup [.handshake] (u32le msg 8)) ?_
    intro entry
    refine ensures_bind _ _ (hbranch .crespNoHandshake entry.isNone) ?_
    intro missing
    cases missing with
    | true => exact hpure none
    | false =>
      cases entry with
      | none => exact hstop _
      | some pair =>
        obtain ⟨owner, pid⟩ := pair
        cases owner with
        | keypair id => exact hstop _
        | handshake own =>
          have hfail : Ensures (do peerPut (some pid); pure (none : Option PeerId))
              TablesSafeWG (fun _ => TablesSafeWG) :=
            ensures_bind _ _ (hput (some pid)) (fun _ => hpure none)
          refine ensures_bind _ _ (hread pid) ?_
          intro p
          refine ensures_bind _ _ (hbranch .crespNotCreatedInitiation _) ?_
          intro notCreated
          cases notCreated with
          | true => exact hfail
          | false =>
            refine ensures_bind _ _ (hephemeral true _ _ _) ?_
            rintro ⟨ck, hash⟩
            refine ensures_bind _ _ (hdh false _ _ _) ?_
            intro ee
            refine ensures_bind _ _ (hbranch .crespEeFailed _) ?_
            intro eeFailed
            cases eeFailed with
            | true => exact hfail
            | false =>
              cases ee with
              | none => exact hstop _
              | some pair =>
                obtain ⟨ck, unused⟩ := pair
                refine ensures_bind _ _ (hdh false _ _ _) ?_
                intro se
                refine ensures_bind _ _ (hbranch .crespSeFailed _) ?_
                intro seFailed
                cases seFailed with
                | true => exact hfail
                | false =>
                  cases se with
                  | none => exact hstop _
                  | some pair =>
                    obtain ⟨ck, unused⟩ := pair
                    refine ensures_bind _ _ (hkdf true true _ _) ?_
                    intro outs
                    refine ensures_bind _ _ (hout outs 0) ?_
                    intro ck
                    refine ensures_bind _ _ (hout outs 1) ?_
                    intro tempHash
                    refine ensures_bind _ _ (hout outs 2) ?_
                    intro key
                    refine ensures_bind _ _ (hdecrypt _ _ _) ?_
                    intro dec
                    refine ensures_bind _ _ (hbranch .crespDecryptFailed _) ?_
                    intro decryptFailed
                    cases decryptFailed with
                    | true => exact hfail
                    | false =>
                      cases dec with
                      | none => exact hstop _
                      | some pair =>
                        obtain ⟨unused, hash⟩ := pair
                        refine ensures_bind _ _ (hread pid) ?_
                        intro current
                        refine ensures_bind _ _ (hbranch .crespStateChanged _) ?_
                        intro changed
                        cases changed with
                        | true => exact hfail
                        | false =>
                          refine ensures_bind _ _ (hread pid) ?_
                          intro last
                          refine ensures_bind _ _ (hset pid _) ?_
                          intro _
                          exact hpure (some pid)

theorem cookieMessageConsume_tables (msg : List UInt8) : Ensures (cookieMessageConsume msg)
    TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hread (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  have hstop {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
  have hset (pid : PeerId) (p : Peer) : Ensures (setPeer pid p) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (setPeer_tables pid p)
  have hput (pid : Option PeerId) : Ensures (peerPut pid) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (peerPut_tables pid)
  have hlookup (kinds : List IndexKind) (index : Nat) :
      Ensures (indexLookup kinds index) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (indexLookup_tables kinds index)
  unfold cookieMessageConsume
  refine ensures_bind _ _ (hlookup [.handshake, .keypair] (u32le msg 4)) ?_
  intro entry
  refine ensures_bind _ _ (hbranch .cookieLookupMiss entry.isNone) ?_
  intro missed
  cases missed with
  | true => exact hpure ()
  | false =>
    cases entry with
    | none => exact hstop "unreachable"
    | some pair =>
      obtain ⟨owner, pid⟩ := pair
      refine ensures_bind _ _ (hread pid) ?_
      intro p
      refine ensures_bind _ _ (hbranch .cookieNoMac1Sent (!p.haveSentMac1)) ?_
      intro absent
      cases absent with
      | true =>
        exact ensures_bind _ _ (hput (some pid)) (fun _ => hpure ())
      | false =>
        refine ensures_bind _ _ (hbranch .cookieDecryptOk _) ?_
        intro decrypted
        cases decrypted with
        | false => exact hput (some pid)
        | true =>
          cases cookie : xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
              ((msg.drop 32).take 32) p.lastMac1Sent with
          | none => exact hstop "unreachable"
          | some bytes =>
            refine ensures_bind _ _ (hambient (AmbientM.hiddenClock64 .cookieBirthdate)) ?_
            intro birthdate
            refine ensures_bind _ _ (hread pid) ?_
            intro current
            refine ensures_bind _ _ (hset pid _) ?_
            intro _
            exact hput (some pid)

end Leanux.Proofs.WG.Index
