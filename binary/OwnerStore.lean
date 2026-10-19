import SourceAdapter
import OwnerWord
import HistoryRegions
import TrustBase

namespace Binary.OwnerWord
open Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- The source setter reloads the current owning Peer. A helper's already
    completed refcount increment is therefore preserved, including when
    owner and referenced peer have the same identity. -/
theorem set_handshake_run (w : World) (device : Device) (id : PeerId) (peer : Peer)
    (word : Option PeerId) (hasDevice : w.wg.dev = some device)
    (hasPeer : device.peers.get? id = some peer) :
    (Source.setPeerWord (.handshake id) word).run w =
      .ok ((), {w with wg := {w.wg with dev := some {device with peers := device.peers.insert id {peer with handshakeEntryPeer := word}}}}) := by
  have peerRead : device.peers[id]? = some peer := hasPeer
  simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind,  pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,       liftWG,  WG.getPeer, WG.getDev, WG.setPeer,   WG.modifyDev, Source.setPeerWord, IndexOwner.setPeerWord,
    hasDevice, peerRead]

theorem set_keypair_run (w : World) (device : Device) (id : KeypairId) (kp : Keypair)
    (word : Option PeerId) (hasDevice : w.wg.dev = some device)
    (hasKeypair : device.keypairs.get? id = some kp) :
    (Source.setPeerWord (.keypair id) word).run w =
      .ok ((), {w with wg := {w.wg with dev := some {device with keypairs := device.keypairs.insert id {kp with peer := word}}}}) := by
  have keyRead : device.keypairs[id]? = some kp := hasKeypair
  simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind,  pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,       liftWG,   WG.getDev,  WG.getKeypair, WG.setKeypair, WG.modifyDev, Source.setPeerWord, IndexOwner.setPeerWord,
    hasDevice, keyRead]

def stored (s : MachineData) : MachineData :=
  {s with dmem := s.dmem.storeInt s.regs.rbx.toBitVec 8 s.regs.rax.toBitVec.toInt}

/-- Actual lookup MOV at +0xba, retaining its one successor in the history.
    NULL and non-NULL results share this instruction theorem. -/
theorem store_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (peers : PeerId → BitVec 64) (s : MachineData) (old : Option PeerId)
    (represented : Field peers s.dmem s.regs.rbx.toBitVec old)
    (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨stored s, Image.Lookup.entry+0xbd⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, Image.Lookup.entry+0xba⟩, history⟩ := by
  refine instruction_history fetch ⟨s, Image.Lookup.entry+0xba⟩ history
    (fun t => t = ⟨stored s, Image.Lookup.entry+0xbd⟩) ?_
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0xba) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, AddrExpr.interp, ConstExpr.interp,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
    Effects.All, BitVec.toAddressSize, BitVec.signed,  BitVec.ofInt_toInt,
    stored, Field] at represented ⊢
  rw [represented]
  simp [Effects.All]
  rfl

theorem stored_field (peers : PeerId → BitVec 64) (s : MachineData) (word : Option PeerId)
    (result : s.regs.rax.toBitVec = pointer peers word) :
    Field peers (stored s).dmem s.regs.rbx.toBitVec word := by
  change Field peers (s.dmem.storeInt s.regs.rbx.toBitVec 8 s.regs.rax.toBitVec.toInt) _ word
  rw [result]
  exact Field.store _ _ _ _

theorem stored_frame (s : MachineData) :
    EqualOutside (InRange s.regs.rbx.toBitVec 8) s.dmem (stored s).dmem :=
  storeInt_frame _ _ _ _

#print axioms set_handshake_run
#print axioms set_keypair_run
#print axioms store_history
#print axioms stored_field
#print axioms stored_frame
end Binary.OwnerWord
