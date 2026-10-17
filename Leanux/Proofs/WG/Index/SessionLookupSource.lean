import Leanux.Proofs.WG.Index.SessionCoherenceSource
import Leanux.Proofs.WG.Index.OwnerCoherenceSessionClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Actual session creation followed, only on success, by its old-index lookup.
The composition retains every Stop from either original operation. -/
def sessionThenLookup (pid : PeerId) (index : Nat) : WG.M (Bool × Option (IndexOwner × PeerId)) := do
  let begun ← beginSession pid
  let hit ← if begun then indexLookup [.keypair] index else pure none
  return (begun, hit)

/-- A coherent published keypair row cannot normally miss or return another
owner/peer. Reference overflow remains a Stop, with no entry ceiling assumed. -/
theorem indexLookup_published (pid : PeerId) (id : KeypairId) (index : Nat) (d : Device)
    (safe : DeviceTablesSafe d) (coherent : HashedOwnersCoherent d)
    (published : {index, owner := IndexOwner.keypair id} ∈ d.indexTable)
    (word : ownerWord d (.keypair id) = some (some pid)) :
    Ensures (indexLookup [.keypair] index) (fun g => g.dev = some d)
      (fun result _ => result = some (.keypair id, pid)) := by
  have found : d.indexTable.find? (·.index == index) = some {index, owner := .keypair id} := by
    cases selected : d.indexTable.find? (·.index == index) with
    | none =>
      have absent := List.find?_eq_none.mp selected
      have impossible := absent _ published
      simp at impossible
    | some e =>
      have numeric : e.index = index := by simpa using List.find?_some selected
      have same := table_field_injective IndexEntry.index safe.1
        (List.mem_of_find?_eq_some selected) published numeric
      simp only [same]
  intro g ambient result final after device run
  cases result with
  | none =>
    obtain ⟨_,_,cause,facts,_⟩ := indexLookup_none [.keypair] index d g ambient none final after device run rfl
    cases cause with
    | absentOrDisallowed =>
      have impossible := facts.1 _ found
      change true = false at impossible
      cases impossible
    | nullOwnerWord =>
      obtain ⟨owner,selected,_,null,_⟩ := facts
      have same : owner = .keypair id := by simpa [found] using selected.symm
      subst owner
      simp [word] at null
    | zeroReference =>
      obtain ⟨owner,target,p,selected,_,actualWord,resident,zero,_⟩ := facts
      obtain ⟨other,q,expected,stored,positive,_⟩ :=
        coherent {index,owner} (List.mem_of_find?_eq_some selected)
      have same : other = target := Option.some.inj (Option.some.inj (expected.symm.trans actualWord))
      subst other
      have samePeer : q = p := Option.some.inj (stored.symm.trans resident)
      subst q
      omega
  | some pair =>
    obtain ⟨owner,target⟩ := pair
    obtain ⟨selected,_,actualWord,_⟩ :=
      indexLookup_success [.keypair] index d g ambient (some (owner,target)) final after device run owner target rfl
    have same : owner = .keypair id := by simpa [found] using selected.symm
    subst owner
    have samePeer : target = pid := Option.some.inj (Option.some.inj (actualWord.symm.trans word))
    subst target
    rfl

/-- Actual successful publication and subsequent lookup, with final invariants
measured after lookup. Freshness is an explicit lifecycle obligation: the
SessionAlias witness shows the other local invariants do not establish it.
False session returns preserve Device only, not the Ambient log or all state. -/
theorem sessionThenLookup_spec (pid : PeerId) (index : Nat) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (safe : DeviceTablesSafe d)
    (coherent : HashedOwnersCoherent d)
    (handshake : {index, owner := IndexOwner.handshake pid} ∈ d.indexTable)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Ensures (sessionThenLookup pid index) (fun g => g.dev = some d)
      (fun result g => ∃ final, g.dev = some final ∧ DeviceTablesSafe final ∧
        HashedOwnersCoherent final ∧
        (result.1 = false → result.2 = none ∧ final = d) ∧
        (result.1 = true → result.2 = some (.keypair d.nextKeypairId,pid))) := by
  have self : p.handshakeEntryPeer = some pid := by
    obtain ⟨target,q,word,found,_,identity⟩ := coherent _ handshake
    change target = pid at identity
    subst target
    simpa [ownerWord,resident] using word
  intro g ambient result out after device run
  change (((beginSession pid).run g).run ambient >>= fun ((begun,middle),inputs) =>
    (((do let hit ← if begun then indexLookup [.keypair] index else pure none
          pure (begun,hit)) : WG.M _).run middle).run inputs) = _ at run
  cases sessionRun : ((beginSession pid).run g).run ambient with
  | error stop => rw [sessionRun] at run; cases run
  | ok triple =>
    obtain ⟨⟨begun,middle⟩,inputs⟩ := triple
    rw [sessionRun] at run
    obtain ⟨published,deviceMiddle,safeMiddle,installed⟩ :=
      beginSession_coherence pid d p resident safe self fresh g ambient begun middle inputs device sessionRun
    have coherentMiddle : HashedOwnersCoherent published := by
      apply beginSession_owner_coherent pid d p resident safe.2.2 fresh g ambient begun middle inputs
        ⟨device,?_⟩ sessionRun published deviceMiddle
      intro initial present
      change g.dev = some initial at present
      rw [device] at present
      cases present
      exact coherent
    cases begun with
    | false =>
      obtain ⟨unchanged,present,effect⟩ := beginSession_effect pid d p g.keypairCounter resident
        g ambient false middle inputs ⟨device,rfl⟩ sessionRun
      have same : unchanged = d := effect.1
      have equal : published = d := by rw [deviceMiddle] at present; cases present; exact same
      subst published
      simp only [pure_bind] at run
      cases run
      exact ⟨d,deviceMiddle,safe,coherent,fun _ => ⟨rfl,rfl⟩,by simp⟩
    | true =>
      obtain ⟨key,caller,number,keyFound,keyWord,_,_,_,oldRow,newRow,_⟩ := installed rfl
      have rowSame := table_field_injective IndexEntry.owner safe.2.1 oldRow handshake rfl
      have sameNumber : number = index := congrArg IndexEntry.index rowSame
      subst number
      have ownerWord : ownerWord published (.keypair d.nextKeypairId) = some (some pid) := by
        simp [Index.ownerWord,keyFound,keyWord]
      change (((indexLookup [.keypair] index).run middle).run inputs >>= fun ((hit,finish),tail) =>
        Except.ok (((true,hit),finish),tail)) = _ at run
      cases lookupRun : ((indexLookup [.keypair] index).run middle).run inputs with
      | error stop => rw [lookupRun] at run; cases run
      | ok triple =>
        obtain ⟨⟨hit,finish⟩,tail⟩ := triple
        rw [lookupRun] at run
        have value := indexLookup_published pid d.nextKeypairId index published safeMiddle coherentMiddle
          newRow ownerWord middle inputs hit finish tail deviceMiddle lookupRun
        obtain ⟨final,present,coherentFinal⟩ := indexLookup_owner_coherence [.keypair] index published
          coherentMiddle middle inputs hit finish tail deviceMiddle lookupRun
        have safeFinal := ((ensures_iff _ _ _).mpr (indexLookup_tables [.keypair] index))
          middle inputs hit finish tail (by
            intro initial present
            rw [deviceMiddle] at present
            cases present
            exact safeMiddle) lookupRun final present
        cases run
        exact ⟨final,present,safeFinal,coherentFinal,by simp,fun _ => value⟩

end Leanux.Proofs.WG.Index
