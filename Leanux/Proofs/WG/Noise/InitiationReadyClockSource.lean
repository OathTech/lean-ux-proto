import Leanux.Proofs.WG.Noise.InitiationReadyWriteSource
import Leanux.Proofs.WG.Noise.InitiationReadyFinishSource
import Leanux.Proofs.WG.Noise.InitiationReadyInputSource

/-! The recorded clock read followed by ordered chain, index and tag writes. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

def afterClock (pid : PeerId) (e encStatic ck key hash : List UInt8) : WG.M (Option (List UInt8)) := do
  let timestamp := tai64n (← hidden .tai64nNow)
  let encTime := aeadEncrypt key noiseNonce timestamp hash
  let h := noiseHash (hash ++ encTime)
  setChain pid ck h
  finish pid e encStatic encTime

theorem afterClock_returns (pid : PeerId) (e encStatic ck key hash : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none)
    (clock : List UInt8) (width : clock.length = 16)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false)
    (g : WGWorld) :
    let encTime := aeadEncrypt key noiseNonce (tai64n clock) hash
    let changed := chainDevice pid d p ck (noiseHash (hash ++ encTime))
    Config.Product.Returns ((afterClock pid e encStatic ck key hash).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient =>
        out = some (le32 1 ++ le32 fresh.value ++ e ++ encStatic ++ encTime ++ List.replicate 32 0) ∧
        current.dev = some {changed with
          peers := changed.peers.insert pid {{p with chainingKey := ck, hash := noiseHash (hash ++ encTime)}
            with handshakeState := HANDSHAKE_CREATED_INITIATION}
          indexTable := {index := fresh.value, owner := .handshake pid} ::
            Index.removeOwner (.handshake pid) d.indexTable} ∧ ambient.hidden = some rest) := by
  dsimp only
  intro ambient pre
  obtain ⟨⟨bytes, afterRead⟩, readAmbient, readRun, value, device, records⟩ :=
    hidden_returns true clock _ width d g ambient pre
  subst bytes
  change ((hidden .tai64nNow : WG.M (List UInt8)).run g).run ambient =
    .ok ((clock, afterRead), readAmbient) at readRun
  let encTime := aeadEncrypt key noiseNonce (tai64n clock) hash
  obtain ⟨⟨u, afterChain⟩, chainAmbient, chainRun, changed, tail⟩ :=
    chain_returns pid d p resident ck (noiseHash (hash ++ encTime)) _
      afterRead readAmbient ⟨device, records⟩
  obtain ⟨⟨out, final⟩, after, finishRun, post⟩ :=
    finish_returns pid e encStatic encTime
      (chainDevice pid d p ck (noiseHash (hash ++ encTime)))
      {p with chainingKey := ck, hash := noiseHash (hash ++ encTime)}
      (by simp [chainDevice]) word collisions fresh rest allCollide isFresh
      afterChain chainAmbient ⟨changed, tail⟩
  refine ⟨(out, final), after, ?_, post⟩
  change (((hidden .tai64nNow : WG.M (List UInt8)).run g).run ambient >>= fun ((bs, current), next) =>
    ((do
      let encTime := aeadEncrypt key noiseNonce (tai64n bs) hash
      setChain pid ck (noiseHash (hash ++ encTime))
      finish pid e encStatic encTime).run current).run next) = _
  rw [readRun]
  change (((setChain pid ck (noiseHash (hash ++ encTime))).run afterRead).run readAmbient >>=
    fun ((_, current), next) => ((finish pid e encStatic encTime).run current).run next) = _
  rw [chainRun]
  exact finishRun

end Leanux.Proofs.WG.Noise.InitiationReady
