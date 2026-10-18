import Leanux.Proofs.WG.HandshakeSecurity.Frames

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged

def latestAt (w : WGWorld) (pid : PeerId) : Option (List UInt8) :=
  (w.dev.bind fun d => d.peers[pid]?).map (·.latestTimestamp)

theorem writeEphemeral_latest (pid : PeerId) (e : List UInt8) (w v : WGWorld)
    (a b : Ambient) (x : Unit)
    (run : ((writeEphemeral pid e).run w).run a = .ok ((x, v), b)) :
    latestAt v pid = latestAt w pid := by
  rw [writeEphemeral, MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p, read, ambient, getter, setter⟩ := run
  obtain ⟨hw, ha, d, hd, hp⟩ := Queues.getPeer_normal pid w read p a ambient getter
  subst read
  subst ambient
  change Except.ok (((), { w with dev := (w.dev.map (fun d =>
    { d with peers := d.peers.insert pid { p with remoteEphemeral := e } })) }), a) =
      .ok ((x, v), b) at setter
  simp only [hd, Option.map_some, Except.ok.injEq, Prod.mk.injEq] at setter
  rw [← setter.1.2]
  simp [latestAt, hd, hp]

theorem guards_same_world (replay : Bool) (lhs now : Int64) (w v : WGWorld)
    (a b : Ambient) (x : Bool)
    (run : ((WG.orM (branch .consumeReplay replay)
      (branchCmp .consumeFlood (lhs > now) lhs.toInt now.toInt)).run w).run a =
        .ok ((x, v), b)) : v = w := by
  cases replay <;> cases run <;> rfl

end Leanux.Proofs.WG.HandshakeSecurity
