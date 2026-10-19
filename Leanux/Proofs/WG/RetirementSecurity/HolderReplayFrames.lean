import Leanux.Proofs.WG.RetirementSecurity.HolderScheduledHandshake

/-! Replay-window and decryption-rejection updates preserve exact native key
credit. The saved getter/setter relationship is checked explicitly, including
the replay loop's bounds failures; no bitmap-shape or authentication premise
is assumed for reference accounting. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderReplay
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem read (id : KeypairId) (P : _→Prop) : Hoare (getKeypair id)
    (fun w=>P (ownershipPointView w))
    (fun k w=>P (ownershipPointView w) ∧ keyReferenceView w id=some (k.internalId,k.refcount)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b entry run
  obtain ⟨rfl,_,d,device,key⟩ := KeyTimes.getKeypair_return id w v k a b run
  exact ⟨entry,by simp [keyReferenceView,keyAt,device,key]⟩

theorem write (id : KeypairId) (k : Keypair) (P : _→Prop) :
    Preserves (fun w=>P (ownershipPointView w) ∧ keyReferenceView w id=some (k.internalId,k.refcount))
      (setKeypair id k) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  cases device:w.dev with
  | none=>simp [keyReferenceView,keyAt,device] at entry
  | some d=>
    cases run
    have refs : keyReferenceView (CounterWindow.store w id k)=keyReferenceView w := by
      funext other
      by_cases same:id=other
      · subst other
        simpa [keyReferenceView,keyAt,CounterWindow.store,device] using entry.2.symm
      · simp [keyReferenceView,keyAt,CounterWindow.store,device,Std.TreeMap.getElem?_insert,same]
    have points : ownershipPointView (CounterWindow.store w id k)=ownershipPointView w := by
      simp only [ownershipPointView,refs]
      simp [CounterWindow.store,device,ownershipAt,peerAt,packetKeyWords]
    change P (ownershipPointView (CounterWindow.store w id k)) ∧
      keyReferenceView (CounterWindow.store w id k) id=some (k.internalId,k.refcount)
    exact ⟨points ▸ entry.1,refs ▸ entry.2⟩

theorem counter_points (id : KeypairId) (nonce : Nat) : SameView ownershipPointView (counterValidate id nonce) := by
  intro initial
  unfold counterValidate
  apply hoare_bind _ _ (read id (·=initial))
  intro k
  let P := fun w=>ownershipPointView w=initial ∧ keyReferenceView w id=some (k.internalId,k.refcount)
  apply hoare_consequence (P:=P) (Q:=fun _=>P) ?_ (fun _ h=>h) (fun _ _ h=>h.1)
  change Preserves P _
  unfold WG.orM
  simp (config:={zeta:=false}) only [branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head setKeypair; exact write _ _ (·=initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec (fun w=>w) P
       intro x b
       change Preserves P _)
    | rx_retention_step

theorem counter (id : KeypairId) (nonce : Nat) : Preserves (HolderAccount temporary) (counterValidate id nonce) :=
  HolderDevice.points_keys (counter_points id nonce)

theorem decrypt (pkt : RxPacket) : Preserves (HolderAccount temporary) (decryptPacket pkt) := by
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) _)
  intro missing
  cases missing with
  | true=>exact preserves_pure _
  | false=>
    apply preserves_bind
      (by
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a result v b before run
        exact (KeyTimes.getKeypair_return _ w v result a b run).1 ▸ before)
    intro k
    apply preserves_bind ((Origins.receiveReject_sameWGWorld k).wp (HolderAccount temporary))
    intro reject
    cases reject with
    | false=>exact (Origins.receiveTail_sameWGWorld pkt k).wp (HolderAccount temporary)
    | true=>
      simpa only [bind_assoc,Bool.true_eq,↓reduceIte,id_eq] using
        preserves_bind
          (key_update_holders pkt.keypair (fun fresh=>{fresh with receiving:={fresh.receiving with isValid:=false}})
            (fun _=>rfl) (fun _=>rfl) temporary)
          (fun _=>preserves_pure (none : Option RxPacket))

end Leanux.Proofs.WG.RetirementSecurity.HolderReplay
