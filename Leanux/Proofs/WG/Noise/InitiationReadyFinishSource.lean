import Leanux.Proofs.WG.Index.DrawRecords
import Leanux.WG.Handshake

/-! Total completion of an initiation: dereference, recorded index insertion,
then the handshake tag and exact message bytes. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Config

def finish (pid : PeerId) (e encStatic encTime : List UInt8) : WG.M (Option (List UInt8)) := do
  _ ← IndexOwner.peerDeref (.handshake pid)
  let index ← indexInsert (.handshake pid)
  setPeer pid {(← getPeer pid) with handshakeState := HANDSHAKE_CREATED_INITIATION}
  return some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)

theorem deref_returns (pid : PeerId) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (stored : PeerId) (word : p.handshakeEntryPeer = some stored)
    (records : Option (List HiddenRecord)) (g : WGWorld) :
    Config.Product.Returns ((IndexOwner.peerDeref (.handshake pid)).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = records)
      (fun (out, current) ambient => out = stored ∧ current.dev = some d ∧ ambient.hidden = records) := by
  intro ambient pre
  refine ⟨(stored, g), ambient, ?_, rfl, pre⟩
  simp [IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev, pre.1, resident, word]
  rfl

def finishTag (pid : PeerId) (index : Nat) (e encStatic encTime : List UInt8) : WG.M (Option (List UInt8)) := do
  setPeer pid {(← getPeer pid) with handshakeState := HANDSHAKE_CREATED_INITIATION}
  return some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)

theorem finishTag_returns (pid : PeerId) (index : Nat) (e encStatic encTime : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (records : Option (List HiddenRecord)) (g : WGWorld) :
    Config.Product.Returns ((finishTag pid index e encStatic encTime).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = records)
      (fun (out, current) ambient =>
        out = some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0) ∧
        current.dev = some {d with peers := d.peers.insert pid {p with handshakeState := HANDSHAKE_CREATED_INITIATION}} ∧
        ambient.hidden = records) := by
  intro ambient pre
  refine ⟨(_, {g with dev := some {d with peers := d.peers.insert pid {p with handshakeState := HANDSHAKE_CREATED_INITIATION}}}), ambient, ?_, rfl, rfl, pre.2⟩
  simp [finishTag, getPeer, getDev, pre.1, resident, setPeer, modifyDev]
  rfl

theorem finish_returns (pid : PeerId) (e encStatic encTime : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false)
    (g : WGWorld) :
    Config.Product.Returns ((finish pid e encStatic encTime).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some (Index.drawStream collisions fresh rest))
      (fun (out, current) ambient =>
        out = some (le32 1 ++ le32 fresh.value ++ e ++ encStatic ++ encTime ++ List.replicate 32 0) ∧
        current.dev = some {d with
          peers := d.peers.insert pid {p with handshakeState := HANDSHAKE_CREATED_INITIATION}
          indexTable := {index := fresh.value, owner := .handshake pid} ::
            Index.removeOwner (.handshake pid) d.indexTable} ∧ ambient.hidden = some rest) := by
  intro ambient pre
  have someWord : ∃ stored, p.handshakeEntryPeer = some stored := by
    cases h : p.handshakeEntryPeer <;> simp_all
  obtain ⟨stored, hword⟩ := someWord
  obtain ⟨⟨storedResult, before⟩, beforeAmbient, readRun, _, device, records⟩ :=
    deref_returns pid d p resident stored hword _ g ambient pre
  obtain ⟨⟨index, tagged⟩, tagAmbient, insertRun, value, inserted, tail⟩ :=
    Index.indexInsert_records (.handshake pid) d collisions fresh rest allCollide isFresh
      before beforeAmbient ⟨device, records⟩
  subst index
  obtain ⟨⟨out, final⟩, after, tagRun, post⟩ :=
    finishTag_returns pid fresh.value e encStatic encTime
      {d with indexTable := {index := fresh.value, owner := .handshake pid} ::
        Index.removeOwner (.handshake pid) d.indexTable} p resident _ tagged tagAmbient ⟨inserted, tail⟩
  refine ⟨(out, final), after, ?_, post⟩
  change (((IndexOwner.peerDeref (.handshake pid)).run g).run ambient >>= fun ((_, current), next) =>
    ((do
      let index ← liftIndex (indexInsert (.handshake pid))
      finishTag pid index e encStatic encTime).run current).run next) = _
  rw [readRun]
  change (((liftIndex (indexInsert (.handshake pid))).run before).run beforeAmbient >>=
    fun ((index, current), next) => ((finishTag pid index e encStatic encTime).run current).run next) = _
  rw [insertRun]
  exact tagRun

end Leanux.Proofs.WG.Noise.InitiationReady
