import Leanux.Proofs.WG.Packets.PublicationIngressFields
import Leanux.Proofs.WG.Packets.PublicationCompletion
import Leanux.Proofs.WG.Origins.OwnerIndex

/-! Native lookup and reference operations preserve the publication anchor and
its epoch-scoped peer frontier. Nullable gets and final payments are retained. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion

theorem preserves_of_geometry {α : Type} (a : WG.M α)
    (shape : SameView OwnerCompletion.geometry a)
    (peers : ∀ initial, Preserves (PeersRetained initial) a)
    (history : List RxHistory.Event) : Preserves (Inv history) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp shape
    w ambient result v finalAmbient hr
  have rx : RxDisposition.nativeRxStore v = RxDisposition.nativeRxStore w := congrArg Prod.snd fields
  have front : frontier v = frontier w := by
    simpa only [frontier,OwnerCompletion.geometry,Option.map_map,Function.comp_def] using
      congrArg (fun s => s.1.map fun p => (p.1,p.2.1)) fields
  have identity := (hoare_iff_run_ambient _ _ _).mp (peers (CurrentIdentity.peerView w))
    w ambient result v finalAmbient (peers_refl w) hr
  exact ⟨hi.1.transport (fun id pkt cell _ => ⟨by simpa only [rx] using cell,
      congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst rx)⟩) (peers_fields identity),
    hi.2.transport rx (FrontiersLe.of_eq front)⟩

/-- The configured view fixes the peer identity fields and peer frontier;
RX contents are retained by their separate concrete source frame. -/
theorem preserves_of_configured {α : Type} (a : WG.M α)
    (rx : SameView RxDisposition.nativeRxStore a)
    (configured : SameView ConfiguredIdentity.view a)
    (history : List RxHistory.Event) : Preserves (Inv history) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have packets := (ProjectedAction.iff_run_ambient _ _ _).mp rx w ambient result v finalAmbient hr
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp configured w ambient result v finalAmbient hr
  have front : frontier v = frontier w := by
    simpa only [ConfiguredIdentity.view,ConfiguredIdentity.state,frontier,Option.map_map,Function.comp_def] using
      congrArg (fun s : Option ConfiguredIdentity.State => s.map fun s => (s.epoch,s.frontier)) fields
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
      (PublicationCompletion.preserves_of_frames a rx
        ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured) configured) history)
      w ambient result v finalAmbient hi.1 hr,
    hi.2.transport packets (FrontiersLe.of_eq front)⟩

theorem store_preserves {α : Type} {a : WG.M α} (store : SameWGStore a)
    (history : List RxHistory.Event) : Preserves (Inv history) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have dev := congrArg WGStoreView.dev ((ProjectedAction.iff_run_ambient _ _ _).mp store w ambient result v finalAmbient hr)
  change v.dev = w.dev at dev
  apply hi.transport_cells
  · intro id pkt cell _
    exact ⟨by simpa only [RxDisposition.nativeRxStore,dev] using cell,
      by simp only [packetStamp,dev]⟩
  · exact FrontiersLe.of_eq (by simp only [frontier,dev])
  · intro pid d p hd hp
    exact ⟨d,p,dev.symm.trans hd,hp,rfl⟩

theorem peerPut_preserves (peer : Option PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (peerPut peer) :=
  preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.peerPay) peer)
    (peerPut_peers peer) history

theorem peerGet_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (peerGet pid) :=
  preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.peerGet_geometry) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.peerGet_peers) pid) history

theorem keypairGet_preserves (kid : Option KeypairId) (history : List RxHistory.Event) :
    Preserves (Inv history) (keypairGet kid) :=
  preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keypairGet_geometry) kid)
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.keypairGet_peers) kid) history

theorem keypairPut_preserves (kid : Option KeypairId) (now : Bool) (history : List RxHistory.Event) :
    Preserves (Inv history) (keypairPut kid now) :=
  preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keyPay) kid now)
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
      (ConfiguredIdentity.keypairPut_view kid now)) history

theorem acquireOwner_preserves (owner : IndexOwner) (history : List RxHistory.Event) :
    Preserves (Inv history) (Affiliation.acquireOwner owner) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have acquisition := Affiliation.acquireOwner_acquisition owner w v result ambient finalAmbient hr
  have rx := RxCredits.loan_rx (RxCredits.acquireOwner_loan owner w v result ambient finalAmbient hr)
  have peers := (ProjectedAction.iff_run_ambient _ _ _).mp
    (CurrentIdentity.acquireOwner_peerView owner) w ambient result v finalAmbient hr
  have retained : PeersRetained (CurrentIdentity.peerView w) v := by
    intro pid ident hv
    simpa only [peers] using hv
  apply hi.transport_cells
  · intro id pkt cell _
    exact ⟨(congrFun (congrArg Prod.snd rx) id).symm.trans cell, congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst rx)⟩
  · intro before after hb ha _
    have fields := acquisition.facts.2
    simp only [Affiliation.view,hb,ha,Option.map_some,Option.some.injEq] at fields
    cases owner <;> exact Nat.le_of_eq (congrArg Affiliation.State.nextPeer fields).symm
  · exact peers_fields retained

theorem acquireOwner_frontier (owner : IndexOwner) : SameView frontier (Affiliation.acquireOwner owner) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hr
  have fields := (Affiliation.acquireOwner_acquisition owner w v result ambient finalAmbient hr).facts.2
  have projected := congrArg (fun s => s.map fun s => (s.epoch,s.nextPeer)) fields
  cases owner <;> simpa only [frontier,Affiliation.view,Affiliation.state,
    Affiliation.State.setWord,Option.map_map,Function.comp_def] using projected

theorem indexLookup_frontier (kinds : List IndexKind) (index : Nat) :
    SameView frontier (indexLookup kinds index) := by
  intro initial
  let P := fun w => frontier w = initial
  have bucket : Preserves P (liftIndex (indexBucket index)) := by
    apply hoare_liftIndex
    intro w d table hi hd
    simpa only [P,frontier,hd,Option.map_some] using hi
  have acquire := fun owner => (acquireOwner_frontier owner).wp (fun s => s = initial)
  change Preserves P _
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  apply preserves_bind bucket
  intro entries
  apply preserves_bind
  · apply list_view_spec id P
    intro entry acc
    rcases acc with ⟨selected,stopped⟩
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .idxWalk true) P)
    intro _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .idxMatch _) P)
    intro matched
    cases matched with
    | false => exact preserves_pure _
    | true =>
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .idxTypeMatch _) P)
      intro kind
      cases kind <;> exact preserves_pure _
  · intro acc
    rcases acc with ⟨entry,stopped⟩
    dsimp only
    have tail : Preserves P (do
        if ← branch .idxFound entry.isSome then
          let some e := entry | do invariant "unreachable"; return none
          let peer ← Affiliation.acquireOwner e.owner
          if ← branch .idxPeerAlive peer.isSome then
            let some pid := peer | do invariant "unreachable"; return none
            return some (e.owner,pid)
        return none) := by
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .idxFound _) P)
      intro found
      cases found with
      | false => exact preserves_pure _
      | true =>
        cases entry with
        | none => exact preserves_bind (hoare_liftAmbient (AmbientM.invariant "unreachable") P) (fun _ => preserves_pure _)
        | some e =>
          apply preserves_bind (acquire e.owner)
          intro peer
          apply preserves_bind (hoare_liftAmbient (AmbientM.branch .idxPeerAlive _) P)
          intro alive
          cases alive with
          | false => exact preserves_pure _
          | true => cases peer with
            | none => exact preserves_bind (hoare_liftAmbient (AmbientM.invariant "unreachable") P) (fun _ => preserves_pure _)
            | some pid => exact preserves_pure _
    cases stopped with
    | false => exact preserves_bind (hoare_liftAmbient (AmbientM.branch .idxWalk false) P) (fun _ => tail)
    | true => exact tail

theorem indexLookup_preserves (kinds : List IndexKind) (index : Nat)
    (history : List RxHistory.Event) : Preserves (Inv history) (indexLookup kinds index) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have rx := RxCredits.loan_rx ((hoare_iff_run_ambient _ _ _).mp
    (RxCredits.indexLookup_loan kinds index w) w ambient result v finalAmbient rfl hr)
  have front := (ProjectedAction.iff_run_ambient _ _ _).mp (indexLookup_frontier kinds index)
    w ambient result v finalAmbient hr
  have identity := (ProjectedAction.iff_run_ambient _ _ _).mp (CurrentIdentity.indexLookup_peerView kinds index)
    w ambient result v finalAmbient hr
  have retained : PeersRetained (CurrentIdentity.peerView w) v := by
    intro pid ident hv
    simpa only [identity] using hv
  refine hi.transport_cells ?_ (FrontiersLe.of_eq front) (peers_fields retained)
  intro id pkt cell _
  exact ⟨(congrFun (congrArg Prod.snd rx) id).symm.trans cell,
    congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst rx)⟩

end Leanux.Proofs.WG.PublicationFrontier
