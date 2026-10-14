import Leanux.Proofs.WG.Config.Validation

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def identityAfter (key : Key) (old : StaticIdentity) : StaticIdentity :=
  let generated := curve25519 key basePoint
  { hasIdentity := if key == nullPoint then false else generated.2,
    staticPrivate := clamp key,
    staticPublic := if key == nullPoint then old.staticPublic else generated.1 }

theorem setStaticIdentity_exact (key : Key) (d : Device) :
    Ensures (setStaticIdentityPrivateKey key) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with staticIdentity := identityAfter key d.staticIdentity }) := by
  rw [ensures_iff]
  mvcgen [setStaticIdentityPrivateKey, generatePublic, requireNotPending,
    getDev, getK, modifyDev, modifyK, branch, invariant, unsupported]
  invariants
  | inv1 => ((⇓? _ w => ⌜w.k.wg = some d⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [identityAfter]

def precomputedAfter (identity : StaticIdentity) (p : Peer) : Key :=
  let generated := curve25519 identity.staticPrivate p.remoteStatic
  if identity.hasIdentity && generated.2 then generated.1 else List.replicate 32 0

theorem precomputeStaticStatic_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (precomputeStaticStatic pid) (fun w => w.k.wg = some d)
      (fun _ w => peerAt w pid = some
        { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p }) := by
  rw [ensures_iff]
  mvcgen [precomputeStaticStatic, requireNotPending, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, precomputedAfter, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals subst_vars
  all_goals simp_all [Std.TreeMap.getElem?_insert, precomputedAfter]
  all_goals subst_vars
  all_goals simp_all

end Leanux.Proofs.WG.Config
