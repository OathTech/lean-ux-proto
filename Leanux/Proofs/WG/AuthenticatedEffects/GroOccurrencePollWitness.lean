import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceAcceptance
import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayPoll

/-! History witnesses travel through native poll control flow. The replay
result is the current counter invocation's result; a branch may discard that
witness, but no later native guard can replace it with an older one. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll.Witness
open Leanux Leanux.WG Leanux.Proofs.Logged GroOccurrence
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

abbrev Good (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E) :=
  GroOccurrence.Accepted candidate record

abbrev Base (good : Entry → List E → Prop) (Safe : List E → Prop) (gro : Buffer) :=
  fun h (_ : World) => Safe h ∧ gro.Ready good h

abbrev AtCounter (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (Safe : List E → Prop) (gro : Buffer) (scope : Nat) (skb : SkbId) (packet : RxPacket) (result : Bool) :=
  fun h (w : World) => Base (Good candidate record) Safe gro h w ∧
    GroOccurrence.Returned candidate record scope skb packet result h

theorem native (action : Leanux.M α) (P : List E → Prop) (Safe : List E → Prop)
    (safe : ∀ h, P h → Safe h) :
    PrefixEnsures (fun h (_ : World) => P h) Safe (liftPrefix action)
      (fun _ h (_ : World) => P h) :=
  PrefixEnsures.lift action (fun h _ input => safe h input) (fun _ _ _ _ input _ => input)

theorem flow_bind (body : PrefixM E α) (next : α → PrefixM E β)
    (contract : PrefixEnsures P S body (fun _ => P))
    (tail : ∀ value, PrefixEnsures P S (next value) Q) :
    PrefixEnsures P S (body >>= next) Q := PrefixEnsures.bind contract tail

theorem branch_bind (decision : Decision) (value : Bool) (P : List E → Prop)
    (Safe : List E → Prop) (next : Bool → PrefixM E α) (safe : ∀ h, P h → Safe h)
    (tail : ∀ result, result = value → PrefixEnsures (fun h (_ : World) => P h) Safe (next result) Q) :
    PrefixEnsures (fun h (_ : World) => P h) Safe
      (liftPrefix (liftWG (branch decision value)) >>= next) Q := by
  apply PrefixEnsures.bind (Q := fun result h (_ : World) => P h ∧ result = value)
  · apply PrefixEnsures.lift _ (fun h _ input => safe h input)
    intro h w result v input run
    cases run
    exact ⟨input,rfl⟩
  · intro result w h input
    exact tail result input.2 w h input.1

theorem stopped (message : String) (next : Unit → PrefixM E α)
    (safe : ∀ h w, P h w → S h) :
    PrefixEnsures P S (liftPrefix (liftWG (invariant message)) >>= next) Q := by
  intro w h input
  exact ⟨[],by change h = h ++ []; simp,safe h w input,True.intro⟩

theorem consume_bind
    (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (Safe : List E → Prop)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (checked : ∀ pid packet endpoint, PrefixPreserves (fun h (_ : World) => Safe h) Safe
      (consume pid packet endpoint))
    (gro : Buffer) (scope : Nat) (skb : SkbId) (packet : RxPacket) (result : Bool)
    (success : result = true) (pid : PeerId) (endpoint : Endpoint)
    (next : Option (List UInt8) → PrefixM E α)
    (tail : ∀ value, PrefixEnsures (fun h w => Base (Good candidate record) Safe gro h w ∧
      ∀ bytes, Good candidate record ⟨scope,skb,packet,bytes⟩ h) Safe (next value) Q) :
    PrefixEnsures (AtCounter candidate record Safe gro scope skb packet result) Safe
      (consume pid packet endpoint >>= next) Q := by
  apply PrefixEnsures.bind _ tail
  have mono : ∀ history suffix,
      (gro.Ready (Good candidate record) history ∧
        ∀ bytes, Good candidate record ⟨scope,skb,packet,bytes⟩ history) →
      (gro.Ready (Good candidate record) (history ++ suffix) ∧
        ∀ bytes, Good candidate record ⟨scope,skb,packet,bytes⟩ (history ++ suffix)) := by
    intro history suffix input
    exact ⟨input.1.append (accepted_monotone candidate record) suffix,
      fun bytes => accepted_monotone candidate record _ history suffix (input.2 bytes)⟩
  apply (remember (Q := fun _ h (_ : World) => Safe h) _ (checked pid packet endpoint)
    (fun h => gro.Ready (Good candidate record) h ∧
      ∀ bytes, Good candidate record ⟨scope,skb,packet,bytes⟩ h) mono).consequence
  · intro _ _ input
    exact ⟨input.1.1,input.1.2,input.2 success⟩
  · intro _ _ _ output
    exact ⟨⟨output.1,output.2.1⟩,output.2.2⟩

theorem receive_option
    (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (Safe : List E → Prop)
    (receive : Buffer → Entry → PrefixM E Buffer)
    (checked : ∀ gro entry, PrefixEnsures
      (fun h w => Base (Good candidate record) Safe gro h w ∧ Good candidate record entry h)
      Safe (receive gro entry) (fun output => Base (Good candidate record) Safe output))
    (gro : Buffer) (scope : Nat) (skb : SkbId) (packet : RxPacket) (out : Option (List UInt8)) :
    PrefixEnsures (fun h w => Base (Good candidate record) Safe gro h w ∧
      ∀ bytes, Good candidate record ⟨scope,skb,packet,bytes⟩ h) Safe
      (forIn out.toList gro (fun bytes buffer => do
        let output ← receive buffer ⟨scope,skb,packet,bytes⟩
        pure (.yield output)))
      (fun output => Base (Good candidate record) Safe output) := by
  cases out with
  | none =>
    exact PrefixEnsures.pure (fun _ _ input => input.1.1) (fun _ _ input => input.1)
  | some bytes =>
    simp only [Option.toList_some,List.forIn_cons,List.forIn_nil,bind_assoc,pure_bind,bind_pure]
    exact (checked gro ⟨scope,skb,packet,bytes⟩).consequence
      (fun _ _ input => ⟨input.1,input.2 bytes⟩) (fun _ _ _ output => output)

theorem leave_bind
    (good : Entry → List E → Prop) (mono : MonotoneWitness good) (Safe : List E → Prop)
    (leave : Nat → PrefixM E Unit)
    (checked : ∀ scope, PrefixPreserves (fun h (_ : World) => Safe h) Safe (leave scope))
    (gro : Buffer) (scope : Nat) (next : Unit → PrefixM E α)
    (before : ∀ h w, P h w → Base good Safe gro h w)
    (tail : ∀ value, PrefixEnsures (Base good Safe gro) Safe (next value) Q) :
    PrefixEnsures P Safe (leave scope >>= next) Q := by
  apply PrefixEnsures.bind _ tail
  apply (remember (Q := fun _ h (_ : World) => Safe h) _ (checked scope) (gro.Ready good)
    (fun _ suffix ready => ready.append mono suffix)).consequence
  · intro h w input; exact before h w input
  · intro _ _ _ output; exact output

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll.Witness
