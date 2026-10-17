import Leanux.Proofs.WG.Noise.ResponseEdgeSource
import Leanux.Proofs.WG.Noise.ConsumeEdges

set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Roaming

/-- A whole successful response consumption takes CREATED_INITIATION to
CONSUMED_RESPONSE on its returned peer. The initial tag is a conclusion of
the actual run, not an entry assumption or a post-lookup substitution. -/
theorem consumeResponse_entry_edge (msg : List UInt8) (before : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeResponse msg) (fun s => s = before)
      (fun result after => ∀ pid, result = some pid →
        before.tagAt pid = some HANDSHAKE_CREATED_INITIATION ∧
        after.tagAt pid = some HANDSHAKE_CONSUMED_RESPONSE) := by
  intro g ambient result final after pre run pid returned
  have finalTag := consumeResponse_tag msg g ambient result final after trivial run pid returned
  rw [← responseWithLookup_erase] at run
  change (((responseWithLookup msg).run g).run ambient >>= fun ((out, current), last) =>
    Except.ok ((out.map (fun pair => pair.2.input.pid), current), last)) = _ at run
  cases observed : ((responseWithLookup msg).run g).run ambient with
  | error err => rw [observed] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, last⟩
    rw [observed] at run
    cases run
    cases out with
    | none => cases returned
    | some pair =>
      have facts := responseWithLookup_facts msg g ambient (some pair) final after
        trivial observed pair rfl
      have pidEq : pair.2.input.pid = pid := Option.some.inj returned
      have prefixFact : ((g.dev.bind fun d => d.peers[pair.1.input.pid]?).map Peer.handshakeState) =
          some pair.1.input.peer.handshakeState := by
        change (((responseLookupPrefix msg).run g).run ambient >>= fun ((entry, current), middle) =>
          ((match entry with
            | none => pure none
            | some entry => do
              let consumed ← responseConsumeTail msg entry.input
              return consumed.map fun out => (entry, out) : WG.M _).run current).run middle) = _ at observed
        cases prefixRun : ((responseLookupPrefix msg).run g).run ambient with
        | error err => rw [prefixRun] at observed; cases observed
        | ok out =>
          rcases out with ⟨⟨entry, current⟩, middle⟩
          rw [prefixRun] at observed
          cases entry with
          | none => cases observed
          | some entry =>
            change (((responseConsumeTail msg entry.input).run current).run middle >>= fun ((consumed, last), ending) =>
              Except.ok ((consumed.map (fun value => (entry, value)), last), ending)) = _ at observed
            cases tailRun : ((responseConsumeTail msg entry.input).run current).run middle with
            | error err => rw [tailRun] at observed; cases observed
            | ok out =>
              rcases out with ⟨⟨consumed, last⟩, ending⟩
              rw [tailRun] at observed
              cases consumed with
              | none => cases observed
              | some consumed =>
                cases observed
                exact responseLookupPrefix_entry_tag msg g.dev g ambient (some entry)
                  current middle rfl prefixRun entry rfl
      have created := facts.1.2.2.2.2.2
      have inputEq := congrArg ResponseInput.pid facts.2.1
      refine ⟨?_, finalTag⟩
      rw [created] at prefixFact
      rw [← pidEq, inputEq]
      rw [← pre]
      exact prefixFact
end Leanux.Proofs.WG.Noise
