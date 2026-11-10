import C1BelowSplitReconstruct
import AllowedipsChildSource

/- Origin: trial source binary-trials/t5/T5Run.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 1 (mirror link): the mirror's three `chooseAndConnectNode` calls of
the intermediate case, run on the device after both allocations, and the projection of
the result. The `hiddenAlloc` half of `allocNode .allocNode234` (the recorded allocation
outcome in the ambient stream) is not run here; `intermediateAllocated` is the device
after `allocNode`'s state update (`nextNode+1`, `nodes.insert id n`). -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG

/-- The mirror device after the leaf's allocation and `list_add_tail` and the
internal node's allocation, before any connection. -/
def intermediateAllocated (d : Device) (key cidr common width pid : Nat) (owner : Peer) : Device :=
  { d with
    nextNode := d.nextNode+1+1
    nodes := (d.nodes.insert d.nextNode (newNode key cidr width (some pid))).insert (d.nextNode+1)
      (newNode key common width none)
    peers := d.peers.insert pid {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} }

/-- Endpoint of the three connections, with the mirror's ordered node writes. -/
def intermediateInstalled (d : Device) (downId b1 b2 parentId direction key cidr common width pid : Nat)
    (downNode parentNode : AipNode) (owner : Peer) : Device :=
  let leaf := newNode key cidr width (some pid)
  let i0 := newNode key common width none
  let i1 := {i0 with bit:=i0.bit.set! b1 (some downId)}
  let i2 := {i1 with bit:=i1.bit.set! b2 (some d.nextNode)}
  { d with
    nextNode := d.nextNode+1+1
    nodes := ((((((((d.nodes.insert d.nextNode leaf).insert (d.nextNode+1) i0).insert downId
        {downNode with parent:=.child (d.nextNode+1) b1}).insert (d.nextNode+1) i1).insert d.nextNode
        {leaf with parent:=.child (d.nextNode+1) b2}).insert (d.nextNode+1) i2).insert (d.nextNode+1)
        {i2 with parent:=.child parentId direction}).insert parentId
        {parentNode with bit:=parentNode.bit.set! direction (some (d.nextNode+1))})
    peers := d.peers.insert pid {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} }

theorem intermediate_connect_run (w : WGWorld) (ambient : Ambient) (d : Device)
    (downId b1 b2 parentId direction key cidr common width pid : Nat)
    (downNode parentNode : AipNode) (owner : Peer)
    (hasDown : d.nodes[downId]?=some downNode) (hasParent : d.nodes[parentId]?=some parentNode)
    (downBelow : downId<d.nextNode) (parentBelow : parentId<d.nextNode)
    (different : downId≠parentId)
    (proper : common<width) (parentProper : parentNode.cidr<parentNode.bitlen)
    (downChoice : b1=downNode.bits/2^(width-1-common)%2)
    (leafChoice : b2=key/2^(width-1-common)%2)
    (parentChoice : direction=key/2^(parentNode.bitlen-1-parentNode.cidr)%2) :
    (((do
      Leanux.WG.liftAip (Leanux.WG.chooseAndConnectNode (d.nextNode+1) downId)
      Leanux.WG.liftAip (Leanux.WG.chooseAndConnectNode (d.nextNode+1) d.nextNode)
      Leanux.WG.liftAip (Leanux.WG.chooseAndConnectNode parentId (d.nextNode+1)) : Leanux.WG.M Unit).run
        {w with dev:=some (intermediateAllocated d key cidr common width pid owner)}).run ambient)=
      .ok (((),{w with dev:=some (intermediateInstalled d downId b1 b2 parentId direction key cidr common
        width pid downNode parentNode owner)}),ambient) := by
  have small1 : ¬1<b1 := by omega
  have small2 : ¬1<b2 := by omega
  have small : ¬1<direction := by omega
  have f1 : d.nextNode≠downId := Ne.symm (Nat.ne_of_lt downBelow)
  have f2 : d.nextNode+1≠downId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt downBelow))
  have f3 : d.nextNode≠parentId := Ne.symm (Nat.ne_of_lt parentBelow)
  have f4 : d.nextNode+1≠parentId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt parentBelow))
  simp [Leanux.WG.chooseAndConnectNode,Leanux.WG.choose,Leanux.WG.getDev,
    Leanux.WG.modifyDev,Leanux.WG.connectNode,Leanux.WG.liftAip,Leanux.WG.getNode,
    Leanux.WG.setNode,Leanux.WG.slotSet,hasDown,hasParent,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem_insert,
    different,f1,f2,f3,f4,Ne.symm f1,Ne.symm f2,
    intermediateInstalled,intermediateAllocated,newNode,←downChoice,←leafChoice,←parentChoice,
    small1,small2,small,Nat.not_le.mpr proper,Nat.not_le.mpr parentProper]

#print axioms intermediate_connect_run

end Binary.Pair.Allowedips.C1Split
