import Leanux.Proofs.WG.Config.MultipartLeaves
import Leanux.Proofs.WG.Config.MultipartSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do



/-- The original peer getter splits after one IPv4 prefix, resumes at its
returned cursor, and feeds both actual fragments to the original coalescer. -/
theorem multipartPeerDump_returns (d : Device) (p : Peer) (a b : NodeId)
    (pid : PeerId) (addr₁ cidr₁ addr₂ cidr₂ : Nat) (parent₁ parent₂ : Slot)
    (ctx : DumpCtx) (firstSkb secondSkb : NlSkb)
    (resident : d.peers[pid]? = some p) (listed : p.allowedipsList = [a, b])
    (distinct : a ≠ b) (endpoint : p.endpoint = none)
    (firstNode : d.nodes[a]? = some { newNode addr₁ cidr₁ 32 (some pid) with parent := parent₁ })
    (secondNode : d.nodes[b]? = some { newNode addr₂ cidr₂ 32 (some pid) with parent := parent₂ })
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0)
    (firstRoom : firstSkb.room = 168) (secondRoom : 72 ≤ secondSkb.room) :
    Campaign2.Returns (multipartPeerDump pid d ctx firstSkb secondSkb)
      (fun s => s.wg.device = some d)
      (fun result s => s.wg.device = some d ∧ result =
        (({ firstSkb with room := 0 },
          { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
          .split (multipartFirst p addr₁ cidr₁)),
         ({ secondSkb with room := secondSkb.room - 72 },
          { ctx with nextAllowedip := none, allowedipsSeq := 0 },
          .complete (multipartLast p addr₂ cidr₂)),
         .ok (multipartJson d p addr₁ cidr₁ addr₂ cidr₂))) := by
  have hf := multipart_getter_returns pid d p ctx firstSkb _ resident
    ((returns_iff _ _ _).mpr (dumpTail_two_split d p a b pid addr₁ cidr₁ addr₂ cidr₂
      parent₁ parent₂ ctx firstSkb listed endpoint firstNode secondNode fresh sequence firstRoom))
  have hs := multipart_getter_returns pid d p
    { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
    secondSkb _ resident
    ((returns_iff _ _ _).mpr (dumpTail_resume d p a b pid addr₂ cidr₂ parent₂
      { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
      secondSkb listed distinct secondNode rfl rfl secondRoom))
  intro entry pre
  obtain ⟨first, afterFirst, firstRun, firstDevice, rfl⟩ := hf entry pre
  obtain ⟨second, afterSecond, secondRun, secondDevice, rfl⟩ := hs afterFirst firstDevice
  refine ⟨_, afterSecond, ?_, secondDevice, rfl⟩
  have okbind {α β : Type} (x : α) (f : α → Except Stop β) :
      ((Except.ok x : Except Stop α) >>= f) = f x := rfl
  simp only [multipartPeerDump, StateT.run_bind, firstRun, okbind, secondRun,
    coalesce_multipart d p addr₁ cidr₁ addr₂ cidr₂ endpoint, StateT.run_pure]
  rfl

end Leanux.Proofs.WG.Config
