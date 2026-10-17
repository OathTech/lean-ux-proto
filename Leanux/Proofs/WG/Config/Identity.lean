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
    Ensures (setStaticIdentityPrivateKey key) (fun w => w.dev = some d)
      (fun _ w => w.dev = some { d with staticIdentity := identityAfter key d.staticIdentity }) := by
  have idle (peers : List PeerId) :
      List.foldlM (fun (_ : Unit) pid => requireNotPending pid "changing the device identity") () peers = (pure () : WG.M Unit) := by
    induction peers with
    | nil => rfl
    | cons pid peers ih => simpa only [List.foldlM_cons, requireNotPending, pure_bind] using ih
  intro g ambient result final after device run
  cases null : key == nullPoint <;>
    simp [setStaticIdentityPrivateKey, idle, getDev, device, generatePublic,
      branch, AmbientM.branch, null, modifyDev] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals simp [identityAfter, null]


def precomputedAfter (identity : StaticIdentity) (p : Peer) : Key :=
  let generated := curve25519 identity.staticPrivate p.remoteStatic
  if identity.hasIdentity && generated.2 then generated.1 else List.replicate 32 0

theorem precomputeStaticStatic_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (precomputeStaticStatic pid) (fun w => w.dev = some d)
      (fun _ w => peerAt w pid = some
        { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p }) := by
  intro g ambient result final after device run
  cases has : d.staticIdentity.hasIdentity <;>
    cases nonNull : (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2 <;>
    simp [precomputeStaticStatic, requireNotPending, getPeer, getDev, device,
      resident, has, nonNull, setPeer, modifyDev, branch, AmbientM.branch] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals simp [peerAt, precomputedAfter, has, nonNull]

end Leanux.Proofs.WG.Config
