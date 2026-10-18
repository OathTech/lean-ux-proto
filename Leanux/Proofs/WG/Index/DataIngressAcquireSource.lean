import Leanux.Proofs.WG.Index.DataIngressReferenceFrames
import Leanux.Proofs.WG.Index.DataIngressRulesSource
import Leanux.Proofs.WG.Config.KeyReferences

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DataIngress
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem positive_front (predicate : Device → Prop) (msg : List UInt8)
    (acquire : ∀d kid key,d.keypairs[kid]?=some key → predicate d →
      predicate (Config.withKeypair d kid {key with refcount:=key.refcount+1}))
    (lookup : Hoare (indexLookup [.keypair] (u32le msg 4)) (DeviceSafe predicate)
      (fun result w=>DeviceSafe predicate w ∧ ∀owner pid,result=some (owner,pid) → ∃kid d p k,
        owner=.keypair kid ∧ w.dev=some d ∧ d.peers[pid]?=some p ∧ 1<p.refcount ∧
        d.keypairs[kid]?=some k ∧ k.peer=some pid ∧ 0<k.refcount)) :
    Hoare (do let entry ← indexLookup [.keypair] (u32le msg 4); Affiliation.receiveKeyAcquire entry)
      (DeviceSafe predicate) (DataIngressRules.Acquired (DeviceSafe predicate) (Held (DeviceSafe predicate)) (Credit (DeviceSafe predicate))) := by
  apply hoare_bind _ _ lookup
  intro entry
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases entry with
  | none =>
    simp [Affiliation.receiveKeyAcquire,keypairGetNull] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact ⟨pre.1,fun _=>⟨pre.1,by simp⟩,by simp⟩
  | some pair =>
    rcases pair with ⟨owner,pid⟩
    obtain ⟨kid,d,p,k,ownerEq,device,resident,peerCount,key,word,keyLive⟩ := pre.2 owner pid rfl
    subst owner
    simp only [Affiliation.receiveKeyAcquire,pure_bind] at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨kp,mid,clock,getKey,finished⟩ := run
    have effect := Config.keypairGet_present kid d k key w a kp mid clock device getKey
    have nonzero : k.refcount≠0 := by omega
    simp only [nonzero,ite_false] at effect
    rcases effect with ⟨rfl,effect⟩
    cases finished
    have core : (DeviceSafe predicate) v := by
      intro actual present
      rw [effect] at present
      cases present
      exact acquire d kid k key (pre.1 d device)
    refine ⟨core,by simp,?_⟩
    intro id target eq
    cases eq
    exact ⟨core,Config.withKeypair d kid {k with refcount:=k.refcount+1},p,
      {k with refcount:=k.refcount+1},effect,resident,peerCount,by simp [Config.withKeypair],by
        change 1<k.refcount+1
        omega⟩

end Leanux.Proofs.WG.Index.DataIngress
