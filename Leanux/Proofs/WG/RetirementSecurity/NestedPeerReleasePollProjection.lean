import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleasePollSource

/-! Exact complete-poll journal projection, including a final release before
an internal Stop. Scope identities follow the existing occurrence mapping. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open GroOccurrencePoll
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem poll_projects (ρ : E → Option F) (scopeMap : Nat → Nat)
    (eg : SkbId → RxPacket → PrefixM E Nat)
    (ea : SkbId → RxPacket → PrefixM F Nat)
    (lg : Nat → PrefixM E Unit) (la : Nat → PrefixM F Unit)
    (sg : {α : Type} → WG.M α → PrefixM E α)
    (sa : {α : Type} → WG.M α → PrefixM F α)
    (pg : Option PeerId → PrefixM E Unit) (pa : Option PeerId → PrefixM F Unit)
    (cg : SkbId → RxPacket → PrefixM E Bool)
    (ca : SkbId → RxPacket → PrefixM F Bool)
    (ug : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (ua : PeerId → RxPacket → Endpoint → PrefixM F (Option (List UInt8)))
    (rg : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM E GroOccurrence.Buffer)
    (ra : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM F GroOccurrence.Buffer)
    (fg : GroOccurrence.Buffer → PrefixM E Unit) (fa : GroOccurrence.Buffer → PrefixM F Unit)
    (he : ∀ skb pkt, ProjectsPrefix ρ scopeMap (eg skb pkt) (ea skb pkt))
    (hl : ∀ token, ProjectsPrefix ρ id (lg token) (la (scopeMap token)))
    (hs : ∀ {α} (action : WG.M α), ProjectsPrefix ρ id (sg action) (sa action))
    (hp : ∀ peer, ProjectsPrefix ρ id (pg peer) (pa peer))
    (hc : ∀ skb pkt, ProjectsPrefix ρ id (cg skb pkt) (ca skb pkt))
    (hu : ∀ pid pkt ep, ProjectsPrefix ρ id (ug pid pkt ep) (ua pid pkt ep))
    (hr : ∀ gro entry, ProjectsPrefix ρ (GroOccurrence.Buffer.map scopeMap) (rg gro entry)
      (ra (gro.map scopeMap) (entry.map scopeMap)))
    (hf : ∀ gro, ProjectsPrefix ρ id (fg gro) (fa (gro.map scopeMap)))
    (pid : PeerId) (budget : Nat) :
    ProjectsPrefix ρ id (pollWith sg pg eg lg cg ug rg fg pid budget)
      (pollWith sa pa ea la ca ua ra fa pid budget) := by
  unfold pollWith
  apply projectsPrefix_bind ρ id id (hs _)
  intro noBudget
  dsimp only [id]
  apply projectsPrefix_ite
  · intro _
    exact projectsPrefix_pure ρ id _
  · intro _
    apply projectsPrefix_bind ρ (mapAccumulator scopeMap) id
    · apply projectsPrefix_range ρ (mapAccumulator scopeMap)
      intro n acc
      dsimp only [mapAccumulator]
      repeat' first
        | with_reducible exact hs _
        | with_reducible exact hp _
        | with_reducible exact hc _ _
        | with_reducible exact hu _ _ _
        | with_reducible exact hl _
        | exact hr _ _
        | (with_reducible apply projectsPrefix_bind ρ scopeMap _ (he _ _); intro token)
        | with_reducible apply projectsPrefix_forIn ρ (GroOccurrence.Buffer.map scopeMap)
        | with_reducible apply projectsPrefix_bind ρ (GroOccurrence.Buffer.map scopeMap)
        | with_reducible apply projectsPrefix_bind ρ id
        | with_reducible apply projectsPrefix_ite
        | (with_reducible intro x; try dsimp only [id, mapAccumulator])
        | (with_reducible split; all_goals try simp_all only [])
        | (simpa only [mapAccumulator, projectStep] using
            projectsPrefix_pure ρ (projectStep (mapAccumulator scopeMap)) _)
        | with_reducible exact projectsPrefix_pure ρ (projectStep (GroOccurrence.Buffer.map scopeMap)) _
        | with_reducible exact projectsPrefix_pure ρ id _
      all_goals try exact fun _ _ => rfl

    · intro acc
      dsimp only [mapAccumulator]
      repeat' first
        | with_reducible exact hs _
        | with_reducible exact hf _
        | with_reducible exact projectsPrefix_pure ρ id _
        | with_reducible apply projectsPrefix_bind ρ id
        | with_reducible apply projectsPrefix_ite
        | (with_reducible intro x; try dsimp only [id])
        | (with_reducible split; all_goals try simp_all only [])

      all_goals exact fun _ _ => rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
