import Leanux.Proofs.WG.Config.AllowedReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem getPeerDump_empty_device (d : Device) (pid : PeerId) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (fresh : ctx.nextAllowedip = none) (room : 168 ≤ skb.room) :
    Returns (getPeerDump pid ctx skb) (fun w => w.dev = some d)
      (fun result w => w.dev = some d ∧ result =
        ({ skb with room := skb.room - peerFixedSpace p },
         { ctx with nextAllowedip := none, allowedipsSeq := 0 },
         .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p })) := by
  have hg : Returns (getPeer pid) (fun w => w.dev = some d)
      (fun q w => q = p ∧ w.dev = some d) := by
    intro g ambient device
    refine ⟨p, g, ambient, ?_, rfl, device⟩
    simp [getPeer, getDev, device, resident]
    rfl
  rw [getPeerDump_source]
  apply returns_bind _ _ hg
  intro q w ambient h
  obtain ⟨same, hd⟩ := h
  subst q
  exact (returns_iff _ _ _).mpr
    (dumpTail_no_allowedips_returns p ctx skb fresh empty room (fun k => k.dev = some d)) w ambient hd

/-- Both numeric setter outcomes are followed by the actual peer dump. Source
exceptions still stop the original bind and are not turned into numeric errors. -/
theorem allowedip_get_after_set (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (addr cidr : Nat) (ctx : DumpCtx) (skb : NlSkb)
    (resident : d.peers[pid]? = some p) (empty : p.allowedipsList = [])
    (root : allowedRootValue v4 d = none) (width : cidr ≤ allowedBits v4)
    (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq + 1)
    (room : 172 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    Ensures (do
      let ret ← setAllowedip pid (allowedAttrs v4 addr cidr)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun s => s.dev = some d)
      (fun result s => ∃ final, s.dev = some final ∧
        EmptyRootInsertEffect v4 d pid p addr cidr result.1 final ∧
        result.2 =
          ({ skb with room := skb.room - (peerFixedSpace p +
             (if result.1 = 0 then 4 + allowedIpSpace (allowedFamily v4) else 0)) },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p ++
             (if result.1 = 0 then [("allowed_ips", Json.arr #[allowedJson v4 addr cidr])] else []) })) := by
  intro entry ambient result final after initial run
  change (((setAllowedip pid (allowedAttrs v4 addr cidr)).run entry).run ambient >>=
    fun ((ret, g), a) => ((getPeerDump pid ctx skb).run g).run a >>=
      fun ((dump, next), a') => Except.ok (((ret, dump), next), a')) = _ at run
  cases hs : ((setAllowedip pid (allowedAttrs v4 addr cidr)).run entry).run ambient with
  | error e => rw [hs] at run; cases run
  | ok output =>
    obtain ⟨⟨ret, w⟩, nextAmbient⟩ := output
    rw [hs] at run
    change (((getPeerDump pid ctx skb).run w).run nextAmbient >>=
      fun ((dump, next), a') => Except.ok (((ret, dump), next), a')) =
        .ok ((result, final), after) at run
    have pre := setAllowedip_empty_root_effect v4 d pid p addr cidr resident root width
      entry ambient ret w nextAmbient initial hs
    obtain ⟨middle, device, effect⟩ := pre
    rcases effect with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨dump, afterDump, afterAmbient, hdump, unchanged, out⟩ :=
        getPeerDump_empty_device (insertSequenceDevice d) pid p ctx skb resident empty fresh (by omega) w nextAmbient device
      rw [hdump] at run
      cases run
      refine ⟨insertSequenceDevice d, unchanged, Or.inl ⟨rfl, rfl⟩, ?_⟩
      simpa [ENOMEM] using out
    · let updated := { p with allowedipsList := [d.nextNode] }
      let inserted := emptyRootInserted v4 (insertSequenceDevice d) pid p addr cidr
      have peer : inserted.peers[pid]? = some updated := by
        simp [inserted, emptyRootInserted, insertSequenceDevice, updated, empty]
      have node : inserted.nodes[d.nextNode]? =
          some { newNode addr cidr (allowedBits v4) (some pid) with parent := allowedRoot v4 } := by
        simp [inserted, emptyRootInserted, insertSequenceDevice]
      have seq : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = inserted.peerAllowedips.seq := by
        cases v4 <;> simpa [inserted, emptyRootInserted, insertSequenceDevice] using sequence
      obtain ⟨dump, afterDump, afterAmbient, hdump, unchanged, out⟩ :=
        getPeerDump_single v4 inserted updated d.nextNode pid addr cidr (allowedRoot v4) ctx skb
          peer rfl node fresh seq room w nextAmbient device
      rw [hdump] at run
      cases run
      refine ⟨inserted, unchanged, Or.inr ⟨rfl, rfl⟩, ?_⟩
      simpa [updated, peerFixedSpace, peerFixedAttrs, Nat.add_assoc] using out

end Leanux.Proofs.WG.Config
