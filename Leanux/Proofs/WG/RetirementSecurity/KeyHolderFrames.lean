import Leanux.Proofs.WG.RetirementSecurity.HolderPayments
import Leanux.Proofs.WG.RetirementSecurity.HolderStoreFrames

/-! Sending-counter increments, validity changes and receiving-window
updates leave key-reference ownership unchanged when they retain the native
allocation stamp and count. This frame deliberately permits cryptographic
fields to change; it is only an ownership projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def keyReferenceView (w : WGWorld) :=
  fun id : KeypairId => (keyAt w id).map fun k => (k.internalId,k.refcount)

theorem Credits.Exact.reference_view (account : Credits.Exact credits w)
    (same : keyReferenceView v = keyReferenceView w) : Credits.Exact credits v := by
  intro allocation
  have fields := congrFun same allocation.slot
  cases old : keyAt w allocation.slot <;> cases current : keyAt v allocation.slot
  all_goals simp only [keyReferenceView,old,current,Option.map_some,Option.map_none,
    Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at fields
  · simpa [Credits.balance,old,current] using account allocation
  · obtain ⟨stamp,count⟩ := fields
    simpa [Credits.balance,old,current,stamp,count] using account allocation

theorem HolderAccount.reference_view (account : HolderAccount temporary w)
    (same : keyReferenceView v = keyReferenceView w)
    (carriers : carrierShape v = carrierShape w) : HolderAccount temporary v := by
  obtain ⟨loans,projected,credits⟩ := account
  have after := credits.reference_view same
  refine ⟨loans,durableLoans_transport loans carriers projected ?_,after⟩
  exact durable_resident after

theorem key_update_holders (id : KeypairId) (f : Keypair → Keypair)
    (stamp : ∀ k, (f k).internalId = k.internalId)
    (count : ∀ k, (f k).refcount = k.refcount) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (do let k ← getKeypair id; setKeypair id (f k)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  cases result
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨k,u,c,readRun,setRun⟩ := run
  obtain ⟨world,ambient,d,device,resident⟩ := KeyTimes.getKeypair_return id w u k a c readRun
  subst u
  subst c
  have equality : {w with dev := some {d with keypairs := d.keypairs.insert id (f k)}} = v ∧ a = b := by
    simpa [setKeypair,modifyDev,device] using setRun
  obtain ⟨rfl,rfl⟩ := equality
  apply account.reference_view
  · funext other
    by_cases same : id = other
    · subst other
      simp [keyReferenceView,keyAt,device,resident,stamp,count]
    · simp [keyReferenceView,keyAt,device,Std.TreeMap.getElem?_insert,same]
  · simp [carrierShape,peersAt,device]

end Leanux.Proofs.WG.RetirementSecurity
