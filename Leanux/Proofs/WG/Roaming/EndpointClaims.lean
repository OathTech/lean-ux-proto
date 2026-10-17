import Leanux.Proofs.WG.Roaming.Frames
import Leanux.Proofs.WG.Config.BranchSource
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setPeerEndpoint_destination (pid : PeerId) (e : Endpoint)
    (valid : e.family = AF_INET ∨ e.family = AF_INET6) :
    Ensures (setPeerEndpoint pid e) (fun _ => True)
      (fun _ g => destinationAt g pid = some (destination e)) := by
  let R : Unit → WGWorld → Prop := fun _ g => destinationAt g pid = some (destination e)
  have hbranch (site : Decision) (value : Bool) (S : WGWorld → Prop)
      (f : Bool → WG.M Unit) (hf : Ensures (f value) S R) :
      Ensures ((branch site value : WG.M Bool) >>= f) S R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (Leanux.Proofs.WG.Config.branch_state_spec S site value)) ?_
    intro b g ambient x g' ambient' hp hr
    rcases hp with ⟨rfl, hp⟩
    exact hf g ambient x g' ambient' hp hr
  have hwrite : Ensures (do
      setPeer pid { (← getPeer pid) with endpoint := some e }
      dstCacheReset pid) (fun _ => True) R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid (fun _ => True))) ?_
    intro p
    refine ensures_bind (Q := R) _ _ ?_ ?_
    · intro g ambient result g' ambient' hp hr
      change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
        {d with peers := d.peers.insert pid {p with endpoint := some e}})}), ambient) = _ at hr
      cases hr
      cases hd : g.dev with
      | none => simp [peerAt, hd] at hp
      | some d => simp [R, destinationAt, peerAt]
    · intro _
      exact (ensures_iff _ _ _).mpr (dstCacheReset_destination pid (some (destination e)))
  have hfamily : Ensures (do
      if ← branch .setEndpointV4 (e.family == AF_INET) then
        setPeer pid { (← getPeer pid) with endpoint := some e }
        dstCacheReset pid
      else if ← branch .setEndpointV6 (e.family == AF_INET6) then
        setPeer pid { (← getPeer pid) with endpoint := some e }
        dstCacheReset pid) (fun _ => True) R := by
    refine hbranch _ _ _ _ ?_
    rcases valid with v4 | v6
    · simpa [v4] using hwrite
    · simp only [v6, AF_INET, AF_INET6, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
      refine hbranch _ _ _ _ ?_
      exact hwrite
  have hread : Ensures (getPeer pid) (fun _ => True)
      (fun p g => destinationAt g pid = p.endpoint.map destination) := by
    intro g ambient p g' ambient' hp hr
    have found := ((ensures_iff _ _ _).mpr (getPeer_spec pid (fun _ => True))
      g ambient p g' ambient' hp hr).2
    simp [destinationAt, found]
  unfold setPeerEndpoint
  simp only [requireNotPending, pure_bind]
  refine ensures_bind _ _ hread ?_
  intro p
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (endpointEq_destination
      (fun g => destinationAt g pid = p.endpoint.map destination) e p.endpoint valid)) ?_
  intro equal
  refine hbranch _ _ _ _ ?_
  cases equal with
  | true =>
    intro g ambient result g' ambient' hp hr
    cases hr
    exact hp.1.trans (hp.2 rfl)
  | false =>
    intro g ambient result g' ambient' hp hr
    exact hfamily g ambient result g' ambient' trivial hr

theorem clearPeerEndpointSrc_destination (pid : PeerId)
    (remote : Option (Nat × Nat × Nat × Nat)) :
    Ensures (clearPeerEndpointSrc pid) (fun g => destinationAt g pid = remote)
      (fun _ g => destinationAt g pid = remote) := by
  let P : WGWorld → Prop := fun g => destinationAt g pid = remote
  have hmodify (f : Peer → Peer)
      (same : ∀ p, (f p).endpoint.map destination = p.endpoint.map destination) :
      Ensures (getPeer pid >>= fun p => setPeer pid (f p)) P (fun _ => P) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient result g' ambient' hp hr
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid (f p)})}), ambient) = _ at hr
    cases hr
    have before : p.endpoint.map destination = remote := by
      simpa [P, destinationAt, hp.2] using hp.1
    cases hd : g.dev with
    | none => simp [peerAt, hd] at hp
    | some d => simpa [P, destinationAt, peerAt, same] using before
  unfold clearPeerEndpointSrc dstCacheResetNow
  rw [← bind_assoc]
  refine ensures_bind _ _ (hmodify
    (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}) ?_) ?_
  · intro p
    cases p.endpoint <;> simp [destination]
  · intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (dstCacheReset_destination pid remote)) ?_
    intro _
    exact hmodify (fun p => {p with dstCache := {p.dstCache with slot := none}}) (fun _ => rfl)

theorem setPeerEndpointFromSkb_destination (pid : PeerId) (src : SkbSource) :
    Ensures (setPeerEndpointFromSkb pid src) (fun _ => True)
      (fun _ g => destinationAt g pid = some (destination (sourceEndpoint src))) := by
  unfold setPeerEndpointFromSkb
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (endpointFromSkb_exact src (fun _ => True))) ?_
  intro endpoint g ambient result g' ambient' hp hr
  rcases hp with ⟨_, rfl, family⟩
  have valid : (sourceEndpoint src).family = AF_INET ∨ (sourceEndpoint src).family = AF_INET6 := by
    rcases family with v4 | v6
    · exact Or.inl (by simp [sourceEndpoint, v4])
    · exact Or.inr (by simp [sourceEndpoint, v6])
  let next := {ambient with steps := ambient.steps.push {
    decision := .epFromSkbOk, outcome := true, netRx := ambient.netRxSection}}
  have run : ((setPeerEndpoint pid (sourceEndpoint src)).run g).run next =
      .ok ((result, g'), ambient') := by
    simpa [branch, AmbientM.branch, next] using hr
  exact setPeerEndpoint_destination pid (sourceEndpoint src) valid
    g next result g' ambient' trivial run

end Leanux.Proofs.WG.Roaming
