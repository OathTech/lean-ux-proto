import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Noise.InitiationReadySource
import Leanux.Proofs.WG.Noise.InitiationReadyFrames

namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG

/-- Static guards and supplied inputs establish total success of the original
call for every realization, with its exact message, ordered Device writes,
unused hidden suffix and unchanged recorded-timer mode. -/
theorem createInitiation_projected (pid : PeerId) (d : Device) (p : Peer) (mode : Bool)
    (resident : d.peers[pid]? = some p) (identity : d.staticIdentity.hasIdentity = true)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : p.precomputedStaticStatic ≠ List.replicate 32 0)
    (ephemeral clock : List UInt8) (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) p.remoteStatic).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Campaign2.Returns (createInitiation pid)
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest) ∧ s.wg.armRecords = mode)
      (fun out s => out = some (result pid d p ephemeral clock fresh.value).1 ∧
        s.wg.device = some (result pid d p ephemeral clock fresh.value).2 ∧ s.ambient.hidden = some rest ∧ s.wg.armRecords = mode) := by
  intro w pre
  obtain ⟨out, final, run, message, device, records⟩ :=
    createInitiation_total pid d p resident identity word nonnull ephemeral clock randomWidth width
      secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh w ⟨pre.1, pre.2.1⟩
  have preserved := (Noise.ensures_iff _ _ _).mpr (createInitiation_mode mode pid)
    w out final pre.2.2 run
  exact ⟨out, final, run, message, device, records, preserved⟩

end Leanux.Proofs.WG.Noise.InitiationReady
