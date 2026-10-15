import Leanux.Proofs.WG.Config.SuffixReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem coalesce_suffix (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (a : NodeId) (ids : List NodeId) (endpoint : p.endpoint = none) :
    coalesce [.data 2 (deviceFixedAttrs d) (some [multipartFirst p (nodes a).bits (nodes a).cidr]),
      .data 2 [] (some [suffixLast p nodes ids]), .done 2 0] =
      pure (.ok (suffixJson d p nodes (a :: ids))) := by
  have hn : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  simp [coalesce, multipartFirst, suffixLast, suffixJson, peerFixedAttrs, endpoint,
    hn, List.forIn_cons, List.forIn_nil, bind_assoc, List.lookup, ipv4Jsons, ipv4NodeJson]

/-- The original peer getter emits one IPv4 node then resumes its actual cursor
and completes an arbitrary finite resident IPv4 suffix. Only the first two IDs
must differ; repeated IDs later in the suffix are serialized in list order. -/
theorem suffixPeerDump_returns (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (a b : NodeId) (tail : List NodeId) (pid : PeerId)
    (ctx : DumpCtx) (firstSkb secondSkb : NlSkb)
    (resident : d.peers[pid]? = some p) (listed : p.allowedipsList = a :: b :: tail)
    (distinct : a ≠ b) (endpoint : p.endpoint = none)
    (readable : Ipv4Residents d nodes (a :: b :: tail))
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0)
    (firstRoom : firstSkb.room = 168)
    (secondRoom : 44 + 28 * (1 + tail.length) ≤ secondSkb.room) :
    Campaign2.Returns (multipartPeerDump pid d ctx firstSkb secondSkb)
      (fun s => s.wg.device = some d)
      (fun result s => s.wg.device = some d ∧ result =
        (({ firstSkb with room := 0 },
          { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
          .split (multipartFirst p (nodes a).bits (nodes a).cidr)),
         ({ secondSkb with room := secondSkb.room - (44 + 28 * (1 + tail.length)) },
          { ctx with nextAllowedip := none, allowedipsSeq := 0 },
          .complete (suffixLast p nodes (b :: tail))),
         .ok (suffixJson d p nodes (a :: b :: tail)))) := by
  have firstNodes : Ipv4Residents d nodes [a, b] := by
    intro id member
    apply readable id
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with ha | hb
    · exact .inl ha
    · exact .inr (.inl hb)
  have remaining : Ipv4Residents d nodes (b :: tail) := by
    intro id member
    exact readable id (by simp [member])
  have hf := multipart_getter_returns pid d p ctx firstSkb _ resident
    ((returns_iff _ _ _).mpr (dumpTail_suffix_split d nodes p a b tail
      ctx firstSkb listed endpoint firstNodes fresh sequence firstRoom))
  have hs := multipart_getter_returns pid d p
    { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
    secondSkb _ resident
    ((returns_iff _ _ _).mpr (dumpTail_suffix_resume d nodes p a b tail
      { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
      secondSkb listed distinct remaining rfl rfl secondRoom))
  intro entry pre
  obtain ⟨first, afterFirst, firstRun, firstDevice, rfl⟩ := hf entry pre
  obtain ⟨second, afterSecond, secondRun, secondDevice, rfl⟩ := hs afterFirst firstDevice
  refine ⟨_, afterSecond, ?_, secondDevice, rfl⟩
  have okbind {α β : Type} (x : α) (f : α → Except Stop β) :
      ((Except.ok x : Except Stop α) >>= f) = f x := rfl
  simp only [multipartPeerDump, StateT.run_bind, firstRun, okbind, secondRun,
    coalesce_suffix d p nodes a (b :: tail) endpoint, StateT.run_pure]
  rfl

end Leanux.Proofs.WG.Config
