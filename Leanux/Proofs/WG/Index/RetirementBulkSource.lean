import Leanux.Proofs.WG.Index.RetirementBulkEffects
import Leanux.Proofs.WG.Index.RetirementTransferSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- Existing exact source frames retain all saved hashed-owner reservations
through one actual mark, including malformed trie paths whenever it returns. -/
theorem peerMakeDead_allHashedReserved (reserved : Reservations) (pid : PeerId) :
    Preserves (fun w : WGWorld => ∀ d, w.dev = some d → AllHashedReserved reserved d)
      (peerMakeDead pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  have table := peerMakeDead_spec_tableCursor_variant pid _ w a () v b rfl run
  have physical := (BaseRemoval.peerMakeDead_normal pid w v a b run).1
  have peerFrame := congrArg (fun x => x.1.1) physical
  have keys := congrArg (fun x => x.1.2.2.2.1) physical
  have epochFrame := congrArg Prod.fst peerFrame
  intro final out
  cases device : w.dev with
  | none =>
    simp [DecryptCarrier.decryptView,carrierView,peerView,out,device] at epochFrame
  | some d =>
    have epoch : final.ifindex = d.ifindex := by
      simpa only [DecryptCarrier.decryptView,carrierView,peerView,
        out,device,Option.map_some,Option.some.injEq] using epochFrame
    have sameTable : final.indexTable = d.indexTable := by
      have pair : TimerDiscipline.tableCursor final = TimerDiscipline.tableCursor d := by
        simpa only [out,device,Option.map_some,Option.some.injEq] using table
      exact congrArg Prod.fst pair
    have sameWords : ∀ (kid : KeypairId), (final.keypairs[kid]?).map Keypair.peer =
        (d.keypairs[kid]?).map Keypair.peer := by
      intro kid
      simpa only [DecryptCarrier.decryptView,carrierView,keyView,keyWords,
        out,device,Option.bind_some] using congrFun keys kid
    have samePeers : ∀ (pid : PeerId), (final.peers[pid]?).map Peer.internalId =
        (d.peers[pid]?).map Peer.internalId := by
      intro q
      have cells := congrFun (congrArg Prod.snd peerFrame) q
      simpa only [DecryptCarrier.decryptView,carrierView,peerView,out,device,
        Option.bind_some,Option.map_map,Function.comp_def] using
        congrArg (Option.map Prod.fst) cells
    exact allHashedReserved_transport reserved d final (before d device)
      sameTable sameWords samePeers epoch

/-- Only the original first mark pass is composed here. The proof account is
not stepped again; its exact bulk transfer is supplied separately below. -/
theorem saved_mark_allHashedReserved (reserved : Reservations) (saved : List PeerId) :
    Preserves (fun w : WGWorld => ∀ d, w.dev = some d → AllHashedReserved reserved d)
      (for pid in saved do
        _ ← branch .peerRemoveAllIter1 true
        peerMakeDead pid : WG.M Unit) := by
  apply preserves_bind
  · apply list_view_spec id (fun w : WGWorld => ∀ d, w.dev = some d → AllHashedReserved reserved d)
    intro pid acc
    exact preserves_bind (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 true) _) (fun _ =>
      preserves_bind (peerMakeDead_allHashedReserved reserved pid) (fun _ => preserves_pure _))
  · intro _
    exact preserves_pure ()

/-- The actual saved first pass moves the original ordered base occurrences
to the retirement prefix. No distinctness, completion or output-state premise
is added beyond this same normal original pass. -/
theorem saved_makeDead_retirement_step
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (retired ++ loans) w) (stable : StableRx cs w)
    (reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d)
    (run : (((for pid in holders.base.map Owner.slot do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid) : WG.M Unit).run w).run a = .ok (((),v),b)) :
    (holders.withoutBase []).Funded cs ((holders.base ++ retired) ++ loans) v ∧
    StableRx cs v ∧
    (∀ final, v.dev = some final → DeadHashedReserved (holders.base ++ retired) final) := by
  obtain ⟨after,stillStable⟩ := DurableHolders.saved_makeDead_funded funded stable a b run
  have initial : ∀ d, w.dev = some d → AllHashedReserved (holders.base ++ retired) d := by
    intro d device
    exact allHashedReserved_of_funded holders cs (retired ++ loans) retired w d
      configured base funded device (reserved d device)
  have retained := (hoare_iff_run_ambient _ _ _).mp
    (saved_mark_allHashedReserved (holders.base ++ retired) (holders.base.map Owner.slot))
    w a () v b initial run
  refine ⟨?_,stillStable,?_⟩
  · simpa only [List.append_assoc] using after
  · intro d device
    exact deadHashedReserved_of_all _ d (retained d device)

end Leanux.Proofs.WG.Index
