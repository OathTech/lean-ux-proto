import Leanux.Proofs.WG.Keypairs.Frames.Kernel
import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.WGIndex
import Leanux.Proofs.Framing.WGAllowedIps
import Leanux.Proofs.Framing.WGSocketLifecycle

set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Receive-state contracts for the unchanged WireGuard state, queue, trie,
peer and socket helpers. Ordinary keypair allocation/deletion is separate. -/
namespace Leanux.Proofs.WG.Keypairs.WGFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.KernelFrames


/-- Node-only updates retain the legacy receive-state view. -/
theorem sameSnapshot_of_sameNodeKernel (h : Framing.SameNodeKernel a) : SameSnapshot a := by
  intro w x v hr
  have hf := congrArg (fun k => snapshot {w with k}) (h w x v hr)
  simpa [snapshot, Framing.nodeKernelView, Framing.nodeKernel,
    Framing.nodeDevice, Option.bind_map, Function.comp_def] using hf


/-- The socket-control mask retains the legacy receive-state view. -/
theorem sameSnapshot_of_sameSocketKernel (h : Framing.SameSocketKernel a) : SameSnapshot a := by
  intro w x v hr
  have hf := congrArg (fun k => snapshot {w with k}) (h w x v hr)
  simpa [snapshot, Framing.socketKernelView, Framing.socketKernel,
    Framing.socketDevice, Option.bind_map, Function.comp_def] using hf


theorem AipNode_bitAt_sameSnapshot (n : AipNode) (i : Nat) : SameSnapshot (Leanux.WG.AipNode.bitAt n i) := by
  exact sameSnapshot_of_sameKernel (Framing.aipBitAt_sameKernel n i)

theorem AipNode_bitAt_spec (P : Snapshot → Prop) (n : AipNode) (i : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.AipNode.bitAt n i
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (AipNode_bitAt_sameSnapshot n i).wp P

theorem PrevQueue_dequeue_sameSnapshot {α : Type} (q : PrevQueue α) : SameSnapshot (Leanux.WG.PrevQueue.dequeue (α := α) q) := by
  frame_same [Leanux.WG.PrevQueue.dequeue] using []

theorem PrevQueue_dequeue_spec (P : Snapshot → Prop) {α : Type} (q : PrevQueue α) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.PrevQueue.dequeue (α := α) q
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (PrevQueue_dequeue_sameSnapshot (α := α) q).wp P

theorem birthdateTest_sameSnapshot (birthday : Int64) (seconds : Nat) : SameSnapshot (Leanux.WG.birthdateTest birthday seconds) :=
  sameSnapshot_of_sameKernel (Framing.birthdateTest_sameKernel birthday seconds)

theorem birthdateTest_spec (P : Snapshot → Prop) (birthday : Int64) (seconds : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.birthdateTest birthday seconds
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (birthdateTest_sameSnapshot birthday seconds).wp P

theorem birthdateHasExpired_sameSnapshot (birthday : Int64) (seconds : Nat) : SameSnapshot (Leanux.WG.birthdateHasExpired birthday seconds) :=
  sameSnapshot_of_sameKernel (Framing.birthdateHasExpired_sameKernel birthday seconds)

theorem birthdateHasExpired_spec (P : Snapshot → Prop) (birthday : Int64) (seconds : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.birthdateHasExpired birthday seconds
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (birthdateHasExpired_sameSnapshot birthday seconds).wp P

theorem branchExpired_sameSnapshot (d : Decision) (birthday : Int64) (seconds : Nat) (f : Bool → Bool := id) : SameSnapshot (Leanux.WG.branchExpired d birthday seconds f) :=
  sameSnapshot_of_sameKernel (Framing.branchExpired_sameKernel d birthday seconds f)

theorem branchExpired_spec (P : Snapshot → Prop) (d : Decision) (birthday : Int64) (seconds : Nat) (f : Bool → Bool := id) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.branchExpired d birthday seconds f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (branchExpired_sameSnapshot d birthday seconds f).wp P

theorem choose_sameSnapshot (node : AipNode) (key : Nat) : SameSnapshot (Leanux.WG.choose node key) := by
  frame_same [Leanux.WG.choose] using []

theorem choose_spec (P : Snapshot → Prop) (node : AipNode) (key : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.choose node key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (choose_sameSnapshot node key).wp P

theorem commonBits_sameSnapshot (node : AipNode) (key : Nat) (bits : Nat) : SameSnapshot (Leanux.WG.commonBits node key bits) := by
  frame_same [Leanux.WG.commonBits] using []

theorem commonBits_spec (P : Snapshot → Prop) (node : AipNode) (key : Nat) (bits : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.commonBits node key bits
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (commonBits_sameSnapshot node key bits).wp P

theorem endpointEq_sameSnapshot (a : Endpoint) (b : Option Endpoint) : SameSnapshot (Leanux.WG.endpointEq a b) := by
  frame_same [Leanux.WG.endpointEq] using []

theorem endpointEq_spec (P : Snapshot → Prop) (a : Endpoint) (b : Option Endpoint) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.endpointEq a b
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (endpointEq_sameSnapshot a b).wp P

theorem generatePublic_sameSnapshot (secret : Key) : SameSnapshot (Leanux.WG.generatePublic secret) :=
  sameSnapshot_of_sameKernel (Framing.generatePublic_sameKernel secret)

theorem generatePublic_spec (P : Snapshot → Prop) (secret : Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.generatePublic secret
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (generatePublic_sameSnapshot secret).wp P

theorem getDev_sameSnapshot  : SameSnapshot (Leanux.WG.getDev ) := by
  frame_same [Leanux.WG.getDev] using []

theorem getDev_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getDev
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getDev_sameSnapshot ).wp P

theorem newTxSkb_sameSnapshot (p : DataPacket) : SameSnapshot (WG.newTxSkb p) := by
  frame_same [WG.newTxSkb] using [getDev_spec]

theorem newTxSkb_spec (P : Snapshot → Prop) (p : DataPacket) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.newTxSkb p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (newTxSkb_sameSnapshot p).wp P

theorem getTxSkb_sameSnapshot (id : SkbId) : SameSnapshot (WG.getTxSkb id) := by
  frame_same [WG.getTxSkb] using [getDev_spec]

theorem getTxSkb_spec (P : Snapshot → Prop) (id : SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.getTxSkb id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getTxSkb_sameSnapshot id).wp P

theorem setTxSkb_sameSnapshot (id : SkbId) (f : DataPacket → DataPacket) : SameSnapshot (WG.setTxSkb id f) := by
  frame_same [WG.setTxSkb] using [getTxSkb_spec]

theorem setTxSkb_spec (P : Snapshot → Prop) (id : SkbId) (f : DataPacket → DataPacket) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.setTxSkb id f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setTxSkb_sameSnapshot id f).wp P

theorem freeTxSkb_sameSnapshot (id : SkbId) : SameSnapshot (WG.freeTxSkb id) := by
  frame_same [WG.freeTxSkb] using [getTxSkb_spec]

theorem freeTxSkb_spec (P : Snapshot → Prop) (id : SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.freeTxSkb id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeTxSkb_sameSnapshot id).wp P

theorem newRxSkb_sameSnapshot (p : RxPacket) : SameSnapshot (WG.newRxSkb p) := by
  frame_same [WG.newRxSkb] using [getDev_spec]

theorem newRxSkb_spec (P : Snapshot → Prop) (p : RxPacket) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.newRxSkb p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (newRxSkb_sameSnapshot p).wp P

theorem getRxSkb_sameSnapshot (id : SkbId) : SameSnapshot (WG.getRxSkb id) := by
  frame_same [WG.getRxSkb] using [getDev_spec]

theorem getRxSkb_spec (P : Snapshot → Prop) (id : SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.getRxSkb id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getRxSkb_sameSnapshot id).wp P

theorem setRxSkb_sameSnapshot (id : SkbId) (f : RxPacket → RxPacket) : SameSnapshot (WG.setRxSkb id f) := by
  frame_same [WG.setRxSkb] using [getRxSkb_spec]

theorem setRxSkb_spec (P : Snapshot → Prop) (id : SkbId) (f : RxPacket → RxPacket) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.setRxSkb id f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setRxSkb_sameSnapshot id f).wp P

theorem freeRxSkb_sameSnapshot (id : SkbId) : SameSnapshot (WG.freeRxSkb id) := by
  frame_same [WG.freeRxSkb] using [getRxSkb_spec]

theorem freeRxSkb_spec (P : Snapshot → Prop) (id : SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.freeRxSkb id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeRxSkb_sameSnapshot id).wp P

theorem mapM_snapshot_spec (P : Snapshot → Prop) {α β : Type}
    (f : α → M β) (xs : List α)
    (hf : ∀ x, ⦃fun w => ⌜P (snapshot w)⌝⦄ f x
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ xs.mapM f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  have loop (ys : List α) (acc : List β) :
      ⦃fun w => ⌜P (snapshot w)⌝⦄ List.mapM.loop f ys acc
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
    induction ys generalizing acc with
    | nil => mvcgen [List.mapM.loop]
    | cons y ys ih => mvcgen [List.mapM.loop, hf, ih]
  exact loop xs []

theorem indexRemove_sameSnapshot (pid : PeerId) (kind : IndexKind) : SameSnapshot (Leanux.WG.indexRemove pid kind) := by
  intro w x v hr
  have hf := congrArg (fun k => snapshot {w with k})
    (Framing.indexRemove_sameIndexKernel pid kind w x v hr)
  simpa [snapshot, Framing.indexKernelView, Framing.indexKernel,
    Option.bind_map, Function.comp_def] using hf

theorem indexRemove_spec (P : Snapshot → Prop) (pid : PeerId) (kind : IndexKind) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.indexRemove pid kind
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (indexRemove_sameSnapshot pid kind).wp P

theorem keypairPutNull_sameSnapshot  : SameSnapshot (Leanux.WG.keypairPutNull ) := by
  frame_same [Leanux.WG.keypairPutNull] using []

theorem keypairPutNull_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.keypairPutNull
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (keypairPutNull_sameSnapshot ).wp P

theorem mayHaveSlept_sameSnapshot  : SameSnapshot (Leanux.WG.mayHaveSlept ) := by
  frame_same [Leanux.WG.mayHaveSlept] using []

theorem mayHaveSlept_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.mayHaveSlept
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (mayHaveSlept_sameSnapshot ).wp P

theorem raiseLoopbackRx_sameSnapshot  : SameSnapshot (Leanux.WG.raiseLoopbackRx ) := by
  frame_same [Leanux.WG.raiseLoopbackRx] using []

theorem raiseLoopbackRx_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.raiseLoopbackRx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (raiseLoopbackRx_sameSnapshot ).wp P

theorem setNode_sameSnapshot (id : NodeId) (n : AipNode) : SameSnapshot (Leanux.WG.setNode id n) := by
  exact sameSnapshot_of_sameNodeKernel (Framing.setNode_sameNodeKernel id n)

theorem setNode_spec (P : Snapshot → Prop) (id : NodeId) (n : AipNode) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setNode id n
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setNode_sameSnapshot id n).wp P

theorem setPeer_sameSnapshot (id : PeerId) (p : Peer) : SameSnapshot (Leanux.WG.setPeer id p) := by
  frame_same [Leanux.WG.setPeer] using []

theorem setPeer_spec (P : Snapshot → Prop) (id : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setPeer id p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPeer_sameSnapshot id p).wp P

theorem sockFree_sameSnapshot (sock : Option Nat) : SameSnapshot (Leanux.WG.sockFree sock) := by
  exact sameSnapshot_of_sameKernel (Framing.sockFree_sameKernel sock)

theorem sockFree_spec (P : Snapshot → Prop) (sock : Option Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sockFree sock
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sockFree_sameSnapshot sock).wp P

theorem swapEndian_sameSnapshot (bits : Nat) : SameSnapshot (Leanux.WG.swapEndian bits) := by
  frame_same [Leanux.WG.swapEndian] using []

theorem swapEndian_spec (P : Snapshot → Prop) (bits : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.swapEndian bits
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (swapEndian_sameSnapshot bits).wp P

theorem refcountDecAndTest_sameSnapshot (old : Nat) : SameSnapshot (Leanux.refcountDecAndTest old) :=
  sameSnapshot_of_sameKernel (Framing.refcountDecAndTest_sameKernel old)

theorem refcountDecAndTest_spec (P : Snapshot → Prop) (old : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.refcountDecAndTest old
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (refcountDecAndTest_sameSnapshot old).wp P

theorem refcountInc_sameSnapshot (old : Nat) : SameSnapshot (Leanux.refcountInc old) :=
  sameSnapshot_of_sameKernel (Framing.refcountInc_sameKernel old)

theorem refcountInc_spec (P : Snapshot → Prop) (old : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.refcountInc old
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (refcountInc_sameSnapshot old).wp P

theorem refcountIncGuestWide_sameSnapshot (x : OperandExclusion) : SameSnapshot (Leanux.refcountIncGuestWide x) :=
  sameSnapshot_of_sameKernel (Framing.refcountIncGuestWide_sameKernel x)

theorem refcountIncGuestWide_spec (P : Snapshot → Prop) (x : OperandExclusion) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.refcountIncGuestWide x
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (refcountIncGuestWide_sameSnapshot x).wp P

theorem refcountIncNotZero_sameSnapshot (old : Nat) : SameSnapshot (Leanux.refcountIncNotZero old) :=
  sameSnapshot_of_sameKernel (Framing.refcountIncNotZero_sameKernel old)

theorem refcountIncNotZero_spec (P : Snapshot → Prop) (old : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.refcountIncNotZero old
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (refcountIncNotZero_sameSnapshot old).wp P

theorem PrevQueue_peek_sameSnapshot {α : Type} (q : PrevQueue α) : SameSnapshot (Leanux.WG.PrevQueue.peek (α := α) q) := by
  have deq_spec := fun P => PrevQueue_dequeue_spec (α := α) P
  frame_same [Leanux.WG.PrevQueue.peek] using [deq_spec]

theorem PrevQueue_peek_spec (P : Snapshot → Prop) {α : Type} (q : PrevQueue α) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.PrevQueue.peek (α := α) q
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (PrevQueue_peek_sameSnapshot (α := α) q).wp P

theorem allocNode_sameSnapshot (site : AllocSite) (n : AipNode) : SameSnapshot (Leanux.WG.allocNode site n) := by
  frame_same [Leanux.WG.allocNode] using [getDev_spec, hiddenAlloc_snapshot_spec]

theorem allocNode_spec (P : Snapshot → Prop) (site : AllocSite) (n : AipNode) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.allocNode site n
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocNode_sameSnapshot site n).wp P

theorem cookiePrecomputeDeviceKeys_sameSnapshot  : SameSnapshot (Leanux.WG.cookiePrecomputeDeviceKeys ) := by
  frame_same [Leanux.WG.cookiePrecomputeDeviceKeys] using [getDev_spec]

theorem cookiePrecomputeDeviceKeys_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cookiePrecomputeDeviceKeys
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cookiePrecomputeDeviceKeys_sameSnapshot ).wp P

theorem getKeypair_sameSnapshot (id : KeypairId) : SameSnapshot (Leanux.WG.getKeypair id) := by
  frame_same [Leanux.WG.getKeypair] using [getDev_spec]

theorem getKeypair_spec (P : Snapshot → Prop) (id : KeypairId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getKeypair id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getKeypair_sameSnapshot id).wp P

theorem getNode_sameSnapshot (id : NodeId) : SameSnapshot (Leanux.WG.getNode id) := by
  exact sameSnapshot_of_sameKernel (Framing.getNode_sameKernel id)

theorem getNode_spec (P : Snapshot → Prop) (id : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getNode id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getNode_sameSnapshot id).wp P

theorem getPeer_sameSnapshot (id : PeerId) : SameSnapshot (Leanux.WG.getPeer id) := by
  frame_same [Leanux.WG.getPeer] using [getDev_spec]

theorem getPeer_spec (P : Snapshot → Prop) (id : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getPeer id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPeer_sameSnapshot id).wp P

theorem indexBucket_sameSnapshot (index : Nat) : SameSnapshot (Leanux.WG.indexBucket index) :=
  sameSnapshot_of_sameKernel (Framing.indexBucket_sameKernel index)

theorem indexBucket_spec (P : Snapshot → Prop) (index : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.indexBucket index
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (indexBucket_sameSnapshot index).wp P

theorem indexHashed_sameSnapshot (pid : PeerId) (kind : IndexKind) : SameSnapshot (Leanux.WG.indexHashed pid kind) := by
  frame_same [Leanux.WG.indexHashed] using [getDev_spec]

theorem indexHashed_spec (P : Snapshot → Prop) (pid : PeerId) (kind : IndexKind) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.indexHashed pid kind
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (indexHashed_sameSnapshot pid kind).wp P

theorem listDel_sameSnapshot (id : NodeId) : SameSnapshot (Leanux.WG.listDel id) := by
  frame_same [Leanux.WG.listDel] using [getDev_spec, setPeer_spec]

theorem listDel_spec (P : Snapshot → Prop) (id : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.listDel id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (listDel_sameSnapshot id).wp P

theorem loopbackSoftirq_sameSnapshot  : SameSnapshot (Leanux.WG.loopbackSoftirq ) := by
  frame_same [Leanux.WG.loopbackSoftirq] using [getDev_spec, hidden_snapshot_spec, peekHiddenSite_spec, skipCut_spec]

theorem loopbackSoftirq_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.loopbackSoftirq
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (loopbackSoftirq_sameSnapshot ).wp P

theorem prefixMatches_sameSnapshot (node : AipNode) (key bits : Nat) : SameSnapshot (Leanux.WG.prefixMatches node key bits) := by
  frame_same [Leanux.WG.prefixMatches] using [commonBits_spec]

theorem prefixMatches_spec (P : Snapshot → Prop) (node : AipNode) (key bits : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.prefixMatches node key bits
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (prefixMatches_sameSnapshot node key bits).wp P

theorem readNode_sameSnapshot (n : AipNode) : SameSnapshot (Leanux.WG.readNode n) := by
  frame_same [Leanux.WG.readNode] using [swapEndian_spec]

theorem readNode_spec (P : Snapshot → Prop) (n : AipNode) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.readNode n
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (readNode_sameSnapshot n).wp P

theorem socketPort_sameSnapshot (family : Nat) : SameSnapshot (Leanux.WG.socketPort family) := by
  frame_same [Leanux.WG.socketPort] using [getDev_spec]

theorem socketPort_spec (P : Snapshot → Prop) (family : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.socketPort family
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (socketPort_sameSnapshot family).wp P

theorem socketReinit_sameSnapshot (new4 new6 : Option Nat) : SameSnapshot (Leanux.WG.socketReinit new4 new6) := by
  exact sameSnapshot_of_sameSocketKernel (Framing.socketReinit_sameSocketKernel new4 new6)

theorem socketReinit_spec (P : Snapshot → Prop) (new4 new6 : Option Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.socketReinit new4 new6
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (socketReinit_sameSnapshot new4 new6).wp P

theorem armTimer_sameSnapshot (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) : SameSnapshot (Leanux.WG.armTimer pid t delay jc) := by
  frame_same [Leanux.WG.armTimer] using [getPeer_spec, hidden_snapshot_spec, setPeer_spec]

theorem armTimer_spec (P : Snapshot → Prop) (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.armTimer pid t delay jc
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (armTimer_sameSnapshot pid t delay jc).wp P

theorem delTimer_sameSnapshot (pid : PeerId) (t : PeerTimer) : SameSnapshot (Leanux.WG.delTimer pid t) := by
  frame_same [Leanux.WG.delTimer] using [getPeer_spec, setPeer_spec]

theorem delTimer_spec (P : Snapshot → Prop) (pid : PeerId) (t : PeerTimer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.delTimer pid t
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (delTimer_sameSnapshot pid t).wp P

theorem dstCacheGet_sameSnapshot (pid : PeerId) (gen : Nat) : SameSnapshot (Leanux.WG.dstCacheGet pid gen) := by
  frame_same [Leanux.WG.dstCacheGet] using [getPeer_spec, hiddenJiffies_spec, setPeer_spec]

theorem dstCacheGet_spec (P : Snapshot → Prop) (pid : PeerId) (gen : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dstCacheGet pid gen
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dstCacheGet_sameSnapshot pid gen).wp P

theorem dstCacheReset_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.dstCacheReset pid) := by
  frame_same [Leanux.WG.dstCacheReset] using [getPeer_spec, hiddenJiffies_spec, setPeer_spec]

theorem dstCacheReset_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dstCacheReset pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dstCacheReset_sameSnapshot pid).wp P

theorem dstCacheSet_sameSnapshot (pid : PeerId) (src gen dev : Nat) : SameSnapshot (Leanux.WG.dstCacheSet pid src gen dev) := by
  frame_same [Leanux.WG.dstCacheSet] using [getPeer_spec, setPeer_spec]

theorem dstCacheSet_spec (P : Snapshot → Prop) (pid : PeerId) (src gen dev : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dstCacheSet pid src gen dev
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dstCacheSet_sameSnapshot pid src gen dev).wp P

theorem findNode_sameSnapshot (trie : Option NodeId) (bits key : Nat) : SameSnapshot (Leanux.WG.findNode trie bits key) := by
  frame_same [Leanux.WG.findNode] using [AipNode_bitAt_spec, choose_spec, getNode_spec, prefixMatches_spec]

theorem findNode_spec (P : Snapshot → Prop) (trie : Option NodeId) (bits key : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.findNode trie bits key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (findNode_sameSnapshot trie bits key).wp P

theorem freeNode_sameSnapshot (id : NodeId) : SameSnapshot (Leanux.WG.freeNode id) := by
  exact sameSnapshot_of_sameNodeKernel (Framing.freeNode_sameNodeKernel id)

theorem freeNode_spec (P : Snapshot → Prop) (id : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.freeNode id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeNode_sameSnapshot id).wp P

theorem handshakeZero_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.handshakeZero pid) := by
  frame_same [Leanux.WG.handshakeZero] using [getPeer_spec, setPeer_spec]

theorem handshakeZero_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.handshakeZero pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeZero_sameSnapshot pid).wp P

theorem indexReplaceHandshake_sameSnapshot (pid : PeerId) (kp : KeypairId) : SameSnapshot (Leanux.WG.indexReplaceHandshake pid kp) := by
  frame_same [Leanux.WG.indexReplaceHandshake] using [indexHashed_spec]

theorem indexReplaceHandshake_spec (P : Snapshot → Prop) (pid : PeerId) (kp : KeypairId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.indexReplaceHandshake pid kp
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (indexReplaceHandshake_sameSnapshot pid kp).wp P

theorem listAddTail_sameSnapshot (peer : PeerId) (id : NodeId) : SameSnapshot (Leanux.WG.listAddTail peer id) := by
  frame_same [Leanux.WG.listAddTail] using [getPeer_spec, setPeer_spec]

theorem listAddTail_spec (P : Snapshot → Prop) (peer : PeerId) (id : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.listAddTail peer id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (listAddTail_sameSnapshot peer id).wp P

theorem loopbackSend_sameSnapshot (sites : List HiddenSite) (raised : Bool) : SameSnapshot (Leanux.WG.loopbackSend sites raised) := by
  frame_same [Leanux.WG.loopbackSend] using [loopbackSoftirq_spec, raiseLoopbackRx_spec, skipCut_spec]

theorem loopbackSend_spec (P : Snapshot → Prop) (sites : List HiddenSite) (raised : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.loopbackSend sites raised
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (loopbackSend_sameSnapshot sites raised).wp P

theorem nodePlacement_sameSnapshot (trie : Option NodeId) (key cidr bits : Nat) : SameSnapshot (Leanux.WG.nodePlacement trie key cidr bits) := by
  frame_same [Leanux.WG.nodePlacement] using [AipNode_bitAt_spec, choose_spec, getNode_spec, prefixMatches_spec]

theorem nodePlacement_spec (P : Snapshot → Prop) (trie : Option NodeId) (key cidr bits : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.nodePlacement trie key cidr bits
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (nodePlacement_sameSnapshot trie key cidr bits).wp P

theorem requireNotPending_sameSnapshot (pid : PeerId) (what : String) : SameSnapshot (Leanux.WG.requireNotPending pid what) := by
  frame_same [Leanux.WG.requireNotPending] using [getPeer_spec]

theorem requireNotPending_spec (P : Snapshot → Prop) (pid : PeerId) (what : String) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.requireNotPending pid what
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (requireNotPending_sameSnapshot pid what).wp P

theorem resetLastSentHandshake_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.resetLastSentHandshake pid) := by
  frame_same [Leanux.WG.resetLastSentHandshake] using [getPeer_spec, hiddenClock64_spec, setPeer_spec]

theorem resetLastSentHandshake_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.resetLastSentHandshake pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (resetLastSentHandshake_sameSnapshot pid).wp P

theorem rootRemovePeerLists_sameSnapshot (root : NodeId) : SameSnapshot (Leanux.WG.rootRemovePeerLists root) := by
  frame_same [Leanux.WG.rootRemovePeerLists] using [getDev_spec, getNode_spec, getPeer_spec, listDel_spec]

theorem rootRemovePeerLists_spec (P : Snapshot → Prop) (root : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.rootRemovePeerLists root
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (rootRemovePeerLists_sameSnapshot root).wp P

theorem slotGet_sameSnapshot (s : Slot) : SameSnapshot (Leanux.WG.slotGet s) := by
  exact sameSnapshot_of_sameKernel (Framing.slotGet_sameKernel s)

theorem slotGet_spec (P : Snapshot → Prop) (s : Slot) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.slotGet s
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (slotGet_sameSnapshot s).wp P

theorem slotSet_sameSnapshot (s : Slot) (v : Option NodeId) : SameSnapshot (Leanux.WG.slotSet s v) := by
  exact sameSnapshot_of_sameNodeKernel (Framing.slotSet_sameNodeKernel s v)

theorem slotSet_spec (P : Snapshot → Prop) (s : Slot) (v : Option NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.slotSet s v
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (slotSet_sameSnapshot s v).wp P

theorem socketInit_sameSnapshot (port : Nat) : SameSnapshot (Leanux.WG.socketInit port) := by
  exact sameSnapshot_of_sameSocketKernel (Framing.socketInit_sameSocketKernel port)

theorem socketInit_spec (P : Snapshot → Prop) (port : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.socketInit port
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (socketInit_sameSnapshot port).wp P

theorem subtree_sameSnapshot (id : NodeId) : SameSnapshot (Leanux.WG.subtree id) := by
  exact sameSnapshot_of_sameKernel (Framing.subtree_sameKernel id)

theorem subtree_spec (P : Snapshot → Prop) (id : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.subtree id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (subtree_sameSnapshot id).wp P

theorem bucketHas_sameSnapshot (walk collide : Decision) (index : Nat) : SameSnapshot ((pinned_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index) :=
  sameSnapshot_of_sameKernel (Framing.bucketHas_sameKernel walk collide index)

theorem bucketHas_spec (P : Snapshot → Prop) (walk collide : Decision) (index : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (bucketHas_sameSnapshot walk collide index).wp P

theorem connectNode_sameSnapshot (slot : Slot) (id : NodeId) : SameSnapshot (Leanux.WG.connectNode slot id) := by
  frame_same [Leanux.WG.connectNode] using [getNode_spec, setNode_spec, slotSet_spec]

theorem connectNode_spec (P : Snapshot → Prop) (slot : Slot) (id : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.connectNode slot id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (connectNode_sameSnapshot slot id).wp P

theorem dstCacheResetNow_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.dstCacheResetNow pid) := by
  frame_same [Leanux.WG.dstCacheResetNow] using [dstCacheReset_spec, getPeer_spec, setPeer_spec]

theorem dstCacheResetNow_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dstCacheResetNow pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dstCacheResetNow_sameSnapshot pid).wp P

theorem free_sameSnapshot  : SameSnapshot (Leanux.WG.free ) := by
  frame_same [Leanux.WG.free] using [freeNode_spec, getDev_spec, rootRemovePeerLists_spec, subtree_spec]

theorem free_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.free
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (free_sameSnapshot ).wp P

theorem indexInsert_sameSnapshot (pid : PeerId) (kind : IndexKind) : SameSnapshot (Leanux.WG.indexInsert pid kind) :=
  by
  intro w x v hr
  have hf := Framing.indexInsert_sameIndexKernel pid kind w x v hr
  have hs := congrArg (fun k => snapshotOfWGKernelView (Framing.WGKernelView.ofKernel k)) hf
  simpa [snapshotOfWGKernelView, Framing.indexKernelView, Framing.indexKernel,
    Framing.WGKernelView.ofKernel, snapshot, Option.bind_map, Function.comp_def] using hs

theorem indexInsert_spec (P : Snapshot → Prop) (pid : PeerId) (kind : IndexKind) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.indexInsert pid kind
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (indexInsert_sameSnapshot pid kind).wp P

theorem peerGet_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.peerGet pid) := by
  frame_same [Leanux.WG.peerGet] using [getPeer_spec, refcountInc_spec, requireNotPending_spec, setPeer_spec]

theorem peerGet_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerGet pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerGet_sameSnapshot pid).wp P

theorem peerGetMaybeZero_sameSnapshot (peer : Option PeerId) : SameSnapshot (Leanux.WG.peerGetMaybeZero peer) := by
  frame_same [Leanux.WG.peerGetMaybeZero] using [getPeer_spec, refcountIncNotZero_spec, requireNotPending_spec, setPeer_spec]

theorem peerGetMaybeZero_spec (P : Snapshot → Prop) (peer : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerGetMaybeZero peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerGetMaybeZero_sameSnapshot peer).wp P

theorem peerPut_sameSnapshot (peer : Option PeerId) : SameSnapshot (Leanux.WG.peerPut peer) := by
  frame_same [Leanux.WG.peerPut] using [getPeer_spec, indexRemove_spec, refcountDecAndTest_spec, requireNotPending_spec, setPeer_spec]

theorem peerPut_spec (P : Snapshot → Prop) (peer : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerPut peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerPut_sameSnapshot peer).wp P

theorem precomputeStaticStatic_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.precomputeStaticStatic pid) := by
  frame_same [Leanux.WG.precomputeStaticStatic] using [getDev_spec, getPeer_spec, requireNotPending_spec, setPeer_spec]

theorem precomputeStaticStatic_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.precomputeStaticStatic pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (precomputeStaticStatic_sameSnapshot pid).wp P

theorem removeByPeer_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.removeByPeer pid) := by
  frame_same [Leanux.WG.removeByPeer] using [AipNode_bitAt_spec, freeNode_spec, getNode_spec, getPeer_spec, listDel_spec, setNode_spec, slotSet_spec]

theorem removeByPeer_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.removeByPeer pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (removeByPeer_sameSnapshot pid).wp P

theorem setPeerEndpoint_sameSnapshot (pid : PeerId) (e : Endpoint) : SameSnapshot (Leanux.WG.setPeerEndpoint pid e) := by
  frame_same [Leanux.WG.setPeerEndpoint] using [dstCacheReset_spec, endpointEq_spec, getPeer_spec, requireNotPending_spec, setPeer_spec]

theorem setPeerEndpoint_spec (P : Snapshot → Prop) (pid : PeerId) (e : Endpoint) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setPeerEndpoint pid e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPeerEndpoint_sameSnapshot pid e).wp P

theorem setStaticIdentityPrivateKey_sameSnapshot (privateKey : Key) : SameSnapshot (Leanux.WG.setStaticIdentityPrivateKey privateKey) := by
  frame_same [Leanux.WG.setStaticIdentityPrivateKey] using [generatePublic_spec, getDev_spec, requireNotPending_spec]

theorem setStaticIdentityPrivateKey_spec (P : Snapshot → Prop) (privateKey : Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setStaticIdentityPrivateKey privateKey
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setStaticIdentityPrivateKey_sameSnapshot privateKey).wp P

theorem tunnelXmit_sameSnapshot (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) : SameSnapshot ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  frame_same [_private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit] using [loopbackSend_spec, skipCut_spec, socketPort_spec]

theorem tunnelXmit_spec (P : Snapshot → Prop) (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (tunnelXmit_sameSnapshot e bytes ds r exactRx).wp P

theorem chooseAndConnectNode_sameSnapshot (parent node : NodeId) : SameSnapshot (Leanux.WG.chooseAndConnectNode parent node) := by
  frame_same [Leanux.WG.chooseAndConnectNode] using [choose_spec, connectNode_spec, getNode_spec]

theorem chooseAndConnectNode_spec (P : Snapshot → Prop) (parent node : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.chooseAndConnectNode parent node
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (chooseAndConnectNode_sameSnapshot parent node).wp P

theorem clearPeerEndpointSrc_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.clearPeerEndpointSrc pid) := by
  frame_same [Leanux.WG.clearPeerEndpointSrc] using [dstCacheResetNow_spec, getPeer_spec, setPeer_spec]

theorem clearPeerEndpointSrc_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (clearPeerEndpointSrc_sameSnapshot pid).wp P

theorem handshakeInit_sameSnapshot (pid : PeerId) (presharedKey : Option Key) : SameSnapshot (Leanux.WG.handshakeInit pid presharedKey) := by
  frame_same [Leanux.WG.handshakeInit] using [getPeer_spec, precomputeStaticStatic_spec, setPeer_spec]

theorem handshakeInit_spec (P : Snapshot → Prop) (pid : PeerId) (presharedKey : Option Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.handshakeInit pid presharedKey
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeInit_sameSnapshot pid presharedKey).wp P

theorem indexLookup_sameSnapshot (kinds : List IndexKind) (index : Nat) : SameSnapshot (Leanux.WG.indexLookup kinds index) := by
  frame_same [Leanux.WG.indexLookup] using [indexBucket_spec, peerGetMaybeZero_spec]

theorem indexLookup_spec (P : Snapshot → Prop) (kinds : List IndexKind) (index : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.indexLookup kinds index
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (indexLookup_sameSnapshot kinds index).wp P

theorem peerMakeDead_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.peerMakeDead pid) := by
  frame_same [Leanux.WG.peerMakeDead] using [getPeer_spec, removeByPeer_spec, setPeer_spec]

theorem peerMakeDead_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerMakeDead pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerMakeDead_sameSnapshot pid).wp P

theorem pubkeyLookup_sameSnapshot (key : Key) : SameSnapshot (Leanux.WG.pubkeyLookup key) := by
  frame_same [Leanux.WG.pubkeyLookup] using [getDev_spec, peerGetMaybeZero_spec]

theorem pubkeyLookup_spec (P : Snapshot → Prop) (key : Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.pubkeyLookup key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pubkeyLookup_sameSnapshot key).wp P

theorem send4_sameSnapshot (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) : SameSnapshot (Leanux.WG.send4 e cache bytes ds exactRx) := by
  frame_same [Leanux.WG.send4] using [dstCacheGet_spec, dstCacheReset_spec, dstCacheSet_spec, getDev_spec, getPeer_spec, routeLookup_spec, setPeer_spec, tunnelXmit_spec]

theorem send4_spec (P : Snapshot → Prop) (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.send4 e cache bytes ds exactRx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (send4_sameSnapshot e cache bytes ds exactRx).wp P

theorem send6_sameSnapshot (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) : SameSnapshot (Leanux.WG.send6 e cache bytes ds exactRx) := by
  frame_same [Leanux.WG.send6] using [dstCacheGet_spec, dstCacheReset_spec, dstCacheSet_spec, getDev_spec, getPeer_spec, routeLookup_spec, setPeer_spec, tunnelXmit_spec]

theorem send6_spec (P : Snapshot → Prop) (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.send6 e cache bytes ds exactRx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (send6_sameSnapshot e cache bytes ds exactRx).wp P

theorem add_sameSnapshot (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) : SameSnapshot (Leanux.WG.add root bits key cidr peer) := by
  frame_same [Leanux.WG.add] using [AipNode_bitAt_spec, allocNode_spec, chooseAndConnectNode_spec, choose_spec, commonBits_spec, connectNode_spec, freeNode_spec, getNode_spec, listAddTail_spec, listDel_spec, nodePlacement_spec, setNode_spec, slotGet_spec]

theorem add_spec (P : Snapshot → Prop) (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.add root bits key cidr peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (add_sameSnapshot root bits key cidr peer).wp P

theorem peerCreate_sameSnapshot (publicKey : Key) (presharedKey : Option Key) : SameSnapshot (Leanux.WG.peerCreate publicKey presharedKey) := by
  frame_same [Leanux.WG.peerCreate] using [dstCacheReset_spec, getDev_spec, handshakeInit_spec, hiddenAlloc_snapshot_spec, resetLastSentHandshake_spec, setPeer_spec]

theorem peerCreate_spec (P : Snapshot → Prop) (publicKey : Key) (presharedKey : Option Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerCreate publicKey presharedKey
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerCreate_sameSnapshot publicKey presharedKey).wp P

theorem insert_sameSnapshot (family : Nat) (addr cidr : Nat) (peer : PeerId) : SameSnapshot (Leanux.WG.insert family addr cidr peer) := by
  frame_same [Leanux.WG.insert] using [add_spec]

theorem insert_spec (P : Snapshot → Prop) (family : Nat) (addr cidr : Nat) (peer : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.insert family addr cidr peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (insert_sameSnapshot family addr cidr peer).wp P

end Leanux.Proofs.WG.Keypairs.WGFrames
