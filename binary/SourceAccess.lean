import SourceAdapter

/-! Product-world equations for the split mirror's accessors. -/
namespace Binary.Source
open Leanux Leanux.WG

theorem liftAmbient_bind (a : AmbientM α) (f : α → AmbientM β) :
    liftAmbient (a >>= f) = (liftAmbient a >>= fun x => liftAmbient (f x)) := by
  funext w
  simp only [liftAmbient, StateT.run, bind, StateT.bind]
  cases a w.ambient with
  | error e => rfl
  | ok out =>
    rcases out with ⟨v, ambient⟩
    cases f v ambient <;> rfl

theorem hiddenU64_eq (site : HiddenSite) : (hiddenU64 site : Leanux.M Nat) = (do
    let bytes ← hidden site
    pure (bytes.foldr (fun b acc => acc * 256 + b.toNat) 0)) := by
  change liftAmbient (AmbientM.hiddenU64 site) = _
  rw [AmbientM.hiddenU64, liftAmbient_bind]
  rfl

theorem budgetExhausted_ne_ok (name : String) (w : World) (out : α × World) :
    (budgetExhausted name : Leanux.M α).run w ≠ .ok out := by
  cases h : w.ambient.hidden.isSome <;>
    simp [budgetExhausted, AmbientM.budgetExhausted,  AmbientM.unsupported,
       AmbientM.invariant, liftAmbient, StateT.run, bind, StateT.bind,
      pure,  get, getThe, MonadStateOf.get, StateT.get,
      monadLift, MonadLift.monadLift, Except.pure, Except.bind, h] <;> intro bad <;> cases bad

theorem getDev_eq : Source.getDev = (do
    match (← (get : Leanux.M World)).wg.dev with
    | some d => pure d
    | none => invariant "no WireGuard device in this trace's fixture") := by
  funext w
  cases hd : w.wg.dev <;>
    simp [Source.getDev, WG.getDev, StateT.run, liftWG, bind, StateT.bind,
      pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get,
      Except.pure, Except.bind, hd] <;> rfl

theorem getPeer_eq (id : PeerId) : Source.getPeer id = (do
    match (← Source.getDev).peers.get? id with
    | some p => pure p
    | none => invariant s!"dangling peer {id}") := by
  simp only [Source.getPeer, WG.getPeer, Source.liftWG_bind]
  apply Source.bind_congr_right
  intro d
  cases d.peers.get? id <;> rfl

theorem getKeypair_eq (id : KeypairId) : Source.getKeypair id = (do
    match (← Source.getDev).keypairs.get? id with
    | some k => pure k
    | none => invariant s!"dangling keypair {id}") := by
  simp only [Source.getKeypair, WG.getKeypair, Source.liftWG_bind]
  apply Source.bind_congr_right
  intro d
  cases d.keypairs.get? id <;> rfl

theorem ownerWord_eq (owner : IndexOwner) : Source.peerWord owner =
    (match owner with
     | .handshake pid => do return (← Source.getPeer pid).handshakeEntryPeer
     | .keypair kid => do return (← Source.getKeypair kid).peer) := by
  cases owner <;> simp [Source.peerWord, IndexOwner.peerWord, ]

theorem indexBucket_eq (index : Nat) : Source.indexBucket index = (do
    return (← Source.getDev).indexTable.filter (fun e => e.index % 8192 == index % 8192)) := by
  funext w
  cases w with
  | mk ambient tasks seccomp fs wg fixture =>
    cases wg with
    | mk dev => cases dev <;> rfl

theorem modifyDev_run (f : Device → Device) (w : World) :
    (Source.modifyDev f).run w = .ok ((), {w with wg := {w.wg with dev := w.wg.dev.map f}}) := rfl

theorem getNode_eq (id : NodeId) : Source.getNode id = (do
    match (← Source.getDev).nodes.get? id with
    | some n => pure n
    | none => invariant s!"dangling allowedips node {id}") := by
  funext w
  cases hd : w.wg.dev with
  | none =>
    simp [Source.getNode, liftWG, liftAip, WG.getDev, WG.getNode,
      StateT.run, bind, StateT.bind, pure, StateT.pure, get, getThe,
      MonadStateOf.get, StateT.get, Except.pure, Except.bind, getDev_eq, hd]
    rfl
  | some d =>
    cases hn : d.nodes[id]? <;>
      simp [Source.getNode, liftWG, liftAip, WG.getDev, WG.getNode, WG.modifyDev,
        StateT.run, bind, StateT.bind, pure, StateT.pure, get, getThe,
        MonadStateOf.get, StateT.get, Except.pure, Except.bind, getDev_eq, hd,
        liftM, monadLift, MonadLift.monadLift, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.lift, hn] <;> first | rfl | rw [← hd]

end Binary.Source
