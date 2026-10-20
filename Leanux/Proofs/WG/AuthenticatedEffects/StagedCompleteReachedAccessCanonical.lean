import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccessFrames

/-! The key-reference, header and CPU source witnesses unfold the native control flow down
to atomic world accesses and the isolated Ambient/index computations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Access
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

macro "access_source_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | exact Shape.read
  | exact Shape.ambient _
  | (apply Shape.write; apply ReceiveFrames.device <;> intro d <;> rfl)
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def getShape (key : Option KeypairId) : Shape (keypairGet key) := by
  unfold keypairGet getKeypair getDev setKeypair
  simp only [branch,invariant]
  repeat' access_source_step

noncomputable def nullShape : Shape keypairGetNull := by
  unfold keypairGetNull
  simp only [branch]
  repeat' access_source_step

noncomputable def putShape (key : Option KeypairId) (now : Bool) : Shape (keypairPut key now) := by
  have lift (action : IndexM Unit) : (liftM action : WG.M Unit)=liftIndex action := rfl
  simp only [keypairPut,lift,liftIndex,IndexOwner.peerDeref,IndexOwner.peerWord,
    getKeypair,getDev,setKeypair,branch,invariant,unsupported]
  repeat' access_source_step

noncomputable def dsfieldShape (protocol : Nat) (header : List UInt8) : Shape (ipTunnelGetDsfield protocol header) := by
  simp only [ipTunnelGetDsfield,branch,unsupported]
  repeat' access_source_step

noncomputable def cpuShape : Shape cpumaskNextOnline := by
  simp only [cpumaskNextOnline,getDev,branch,invariant]
  repeat' access_source_step

noncomputable def headerShape (msg : List UInt8) : Shape (prepareSkbHeader msg) := by
  simp only [prepareSkbHeader,validateHeaderLen,WG.andM,WG.orM,branch]
  repeat' access_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Access
