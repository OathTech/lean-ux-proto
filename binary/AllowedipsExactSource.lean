import AllowedipsExactTarget

namespace Binary.Pair.Allowedips.Exact
open Leanux Leanux.WG Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps

/-- The mutation fragment of the actual exact branch of WG.add. This runs
the mirror's existing operations; it is not another list implementation. -/
def assignment (id pid : Nat) : WG.M Unit := do
  WG.setNode id { (← WG.getNode id) with peer := some pid }
  WG.listDel id
  WG.listAddTail pid id

theorem assignment_run (k : WGWorld) (d : Device) (ambient : Ambient) (id pid : Nat)
    (old : AipNode) (peer : Peer) (hasDevice : k.dev=some d)
    (hasNode : d.nodes.get? id=some old) (hasPeer : d.peers.get? pid=some peer) :
    ∃ finalAmbient, ((assignment id pid).run k).run ambient=
      .ok (((),{k with dev := some (exactInstalled d id old pid peer)}),finalAmbient) := by
  have nodeRead : ∀ a, ((WG.liftAip (WG.getNode id)).run k).run a=.ok ((old,k),a) := by
    intro a
    rw [liftAip_run,hasDevice]
    have hn : d.nodes[id]?=some old := hasNode
    simp [WG.getNode,hn]
    change Except.ok ((old,{k with dev := some d}),a)=_
    rw [←hasDevice]
  let updated := {d with nodes := d.nodes.insert id {old with peer := some pid}}
  let kw : WGWorld := {k with dev := some updated}
  have nodeWrite : ∀ a, ((WG.liftAip (WG.setNode id {old with peer := some pid})).run k).run a=.ok (((),kw),a) := by
    intro a
    rw [liftAip_run,hasDevice]
    rfl
  obtain ⟨delResult,deleted,a1,delRun,delValue,delState⟩ :=
    (total_iff_run_ambient _ _ _).mp (listDel_wp kw updated rfl id) kw ambient rfl
  subst delResult deleted
  have peerRead : (unlisted updated id).peers[pid]?=some (unlist id peer) := by
    rw [unlisted_get]
    have hp : d.peers[pid]?=some peer := hasPeer
    simp only [updated,hp,Option.map_some]
  obtain ⟨addResult,added,a2,addRun,addValue,addState⟩ :=
    (total_iff_run_ambient _ _ _).mp
      (listAddTail_wp {kw with dev := some (unlisted updated id)} (unlisted updated id) rfl pid id (unlist id peer) peerRead)
      _ a1 rfl
  subst addResult added
  change ∀ a, ((monadLift (WG.getNode id) : WG.M _).run k).run a=.ok ((old,k),a) at nodeRead
  change ∀ a, ((monadLift (WG.setNode id {old with peer := some pid}) : WG.M _).run k).run a=
    .ok (((),kw),a) at nodeWrite
  refine ⟨a2,?_⟩
  simp only [assignment,StateT.run_bind,
    nodeRead,nodeWrite,delRun,addRun,
    Leanux.Proofs.WG.CounterWindow.except_ok_bind]
  rfl

local instance : Labels := Image.linkedLabels

/-- Refinement of the exact mutation fragment, over the full tested
allowed-IPs reconstruction. Entry-to-return insertion and post-heap closure
are separate obligations, not premises hidden in this statement. -/
theorem assignment_simulation (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names o s memory regs k d ambient id base node pid peer owner}
    (hasDevice : k.dev=some d)
    (related : Corresponds names o s.dmem d) (heap : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : effect s=.ok (memory,regs)) :
    ∃ finalWG finalAmbient, ((assignment id pid).run k).run ambient=.ok (((),finalWG),finalAmbient) ∧
      Eventually (instructionStep fetch) (fun t =>
        t.pc=AllowedipsMutationImage.Add.entry+0x549 ∧ t.data.regs=regs ∧
        ∃ finalDevice, finalWG.dev=some finalDevice ∧ Corresponds names o t.data.dmem finalDevice)
        ⟨s,AllowedipsMutationImage.Add.entry+0x3e5⟩ := by
  obtain ⟨a,run⟩ := assignment_run k d ambient id pid node owner hasDevice present hasPeer
  refine ⟨{k with dev := some (exactInstalled d id node pid owner)},a,run,?_⟩
  have finalRelation := effect_corresponds related heap named present peerNamed hasPeer nodeAt peerAt checked
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (effect_segment fetch decoder checked)
  rintro t ⟨pc,mem,reg⟩
  exact ⟨pc,reg,_,rfl,by simpa only [mem] using finalRelation⟩

#print axioms assignment_simulation
end Binary.Pair.Allowedips.Exact
