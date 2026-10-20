import Leanux.Proofs.WG.HandshakeSecurity.LandedH1TagFrames

/-! Native exchange edges obtained from landed H1, with the allocation counter
read from its session effect. No C3 replay history is assumed. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.LandedH1
open Leanux Leanux.WG

private theorem selectedTag (ok : Bool) (pid target : PeerId) (new old : Option Nat) :
    (if ok then if pid = target then new else old else old) =
      (if ok = true ∧ target = pid then new else old) := by
  cases ok <;> by_cases same : pid = target <;> simp [same,eq_comm]

/-- Landed H1 records the exact successful initiation tag update. -/
theorem createInitiation : H1CreateInitiationEdges := by
  intro pid w v a b value run target
  have effect := Noise.createInitiation_tagMap_projected pid (Campaign2.snapshot w a)
    w a value v b rfl run target
  change handshakeTagAt v target =
    (if value.isSome then if pid = target then some HANDSHAKE_CREATED_INITIATION
      else handshakeTagAt w target else handshakeTagAt w target) at effect
  exact effect.trans (selectedTag _ _ _ _ _)

/-- Landed H1 records the exact successful initiation-consumption update. -/
theorem consumeInitiation : H1ConsumeInitiationEdges := by
  intro msg w v a b value run target
  exact Noise.consumeInitiation_tagMap_projected msg (Campaign2.snapshot w a)
    w a value v b rfl run target

/-- Landed H1 supplies both the response precondition and its tag update. -/
theorem createResponse : H1CreateResponseEdges := by
  intro pid w v a b value run
  have effect := Noise.createResponse_tagMap_projected pid (Campaign2.snapshot w a)
    w a value v b rfl run
  refine ⟨effect.2,?_⟩
  intro target
  have tags := effect.1 target
  change handshakeTagAt v target =
    (if value.isSome then if pid = target then some HANDSHAKE_CREATED_RESPONSE
      else handshakeTagAt w target else handshakeTagAt w target) at tags
  exact tags.trans (selectedTag _ _ _ _ _)

/-- Landed H1 supplies the consumed response edge and preserves refusal tags. -/
theorem consumeResponse : H1ResponseEdges := by
  intro msg w v a b value run
  have effect := Noise.consumeResponse_tagMap_projected msg (Campaign2.snapshot w a)
    w a value v b rfl run
  exact ⟨effect.2,effect.1⟩

private theorem sessionCounter (pid : PeerId) (w v : WGWorld) (a b : Ambient) (ok : Bool)
    (run : ((beginSession pid).run w).run a = .ok ((ok,v),b)) :
    v.keypairCounter = w.keypairCounter + (if ok then 1 else 0) := by
  cases device : w.dev with
  | none =>
    simp [beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [beginSession,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨_,_,effect⟩ := Noise.beginSession_effect pid d p w.keypairCounter resident
        w a ok v b ⟨device,rfl⟩ run
      cases ok with
      | false => simpa only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] using effect.2
      | true => exact effect.2.2.2.1

/-- Landed H1's tag and session effects construct the complete local session package. -/
theorem session : H1SessionEffects := by
  intro pid w v a b ok run
  have effect := Noise.beginSession_tagMap_projected pid (Campaign2.snapshot w a)
    w a ok v b rfl run
  refine ⟨effect.2,?_,sessionCounter pid w v a b ok run⟩
  intro target
  have tags := effect.1 target
  change handshakeTagAt v target =
    (if ok then if pid = target then some HANDSHAKE_ZEROED
      else handshakeTagAt w target else handshakeTagAt w target) at tags
  exact tags.trans (selectedTag _ _ _ _ _)

/-- Security dependency: every local H1 exchange and tag premise used by T4's
initialized driver is constructed from campaign 2's landed theorems. -/
theorem driver : H1DriverSourceFacts where
  edges := ⟨createInitiation,consumeInitiation,createResponse,consumeResponse,session⟩
  handshake := handshake
  data := data
  workers := workers
  control := control

end Leanux.Proofs.WG.HandshakeSecurity.LandedH1
