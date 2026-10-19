import Leanux.Proofs.WG.Packets.PublicationFrontier

/-! The real prepare observer establishes the packet frontier at publication,
retains other live packet bounds, and preserves its actual failed journal. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity

/-- The actual ring/decrypt/publication cut never changes the device frontier. -/
theorem prepareSource_frontier : SameView frontier RxWorkers.prepareSource := by
  intro initial
  let P := fun w => frontier w = initial
  have device : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a d v b hi hr
    have same := congrArg WGStoreView.dev ((ProjectedAction.iff_run_ambient _ _ _).mp
      getDev_sameWGStore w a d v b hr)
    change v.dev = w.dev at same
    simpa only [P,frontier,same] using hi
  have ring (queue : PtrRing SkbId) : Preserves P
      (modifyDev fun d => {d with decryptQueue := queue}) := by
    unfold modifyDev
    apply hoare_modify
    intro w hi
    cases hd : w.dev <;> simpa [P,frontier,hd] using hi
  have store (id : SkbId) (out : RxPacket) : Preserves P (setRxSkb id fun _ => out) := by
    unfold setRxSkb
    apply hoare_liftSkb
    intro w d packets hi hd
    simpa only [P,frontier,hd,Option.map_some] using hi
  change Preserves P _
  rw [RxOrigin.prepareSource_factor]
  unfold RxOrigin.prepareWith
  simp only [monadLift_self]
  apply preserves_bind device
  intro dev
  generalize consumed : dev.decryptQueue.consume = item
  rcases item with ⟨item,queue⟩
  cases item with
  | none =>
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decWorkerConsumed false) P)
    intro _
    exact preserves_pure none
  | some id =>
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decWorkerConsumed true) P)
    intro _
    apply preserves_bind (ring queue)
    intro _
    apply preserves_bind ((readDecrypt_frontier id).wp (fun s => s = initial))
    intro pair
    rcases pair with ⟨pkt,decrypted⟩
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decWorkerDecrypted decrypted.isSome) P)
    intro yes
    cases yes with
    | false =>
      apply preserves_bind ((publish_frontier id .dead).wp (fun s => s = initial))
      intro pid
      exact preserves_pure (some pid)
    | true =>
      cases decrypted with
      | none => exact hoare_liftAmbient (AmbientM.invariant "unreachable") P
      | some out =>
        apply preserves_bind (store id out)
        intro _
        apply preserves_bind ((publish_frontier id .crypted).wp (fun s => s = initial))
        intro pid
        exact preserves_pure (some pid)

theorem prepare_frontier (w v : World) (h t : List RxHistory.Event) (value : Option PeerId)
    (hr : runPrefix Origins.HistoryAdapters.prepare w h = (.ok (value,v),t)) :
    frontier v.wg = frontier w.wg := by
  have erased := (Origins.HistoryAdapters.prepare_erases w h).symm.trans (congrArg Prod.fst hr)
  rw [liftWG_run] at erased
  cases native : ((RxWorkers.prepareSource.run w.wg).run w.ambient) with
  | error stop => simp only [native] at erased; cases erased
  | ok out =>
    rcases out with ⟨⟨result,g⟩,ambient⟩
    simp only [native] at erased
    obtain ⟨rfl,rfl⟩ := erased
    exact (ProjectedAction.iff_run_ambient _ _ _).mp prepareSource_frontier
      w.wg w.ambient result g ambient native

/-- Every selected crypted packet gets its bound from its actual checked
entry. Unselected packets use the retained cell and unchanged frontier. -/
theorem prepare_below (w v : World) (h t : List RxHistory.Event) (result : Option PeerId)
    (owner : OwnerChecks.Inv h w) (packets : PeersBelow w.wg)
    (hr : runPrefix Origins.HistoryAdapters.prepare w h = (.ok (result,v),t)) : PeersBelow v.wg := by
  have safe := (OwnerPrepare.prepare w h owner).choose_spec.2.1
  rw [hr] at safe
  cases result with
  | none =>
    obtain ⟨same,_⟩ := PublicationHistory.prepare_none w v h t hr
    rw [same]
    exact packets
  | some pid =>
    obtain ⟨id,r,pre,tail,valid,position,frame,dead,published⟩ :=
      PublicationHistory.prepare_packet_cases w v h t pid hr
    intro after ha slot pkt hp crypted
    have cell : (RxDisposition.nativeRxStore v.wg).2 slot = some pkt := by
      simp [RxDisposition.nativeRxStore,ha,hp]
    by_cases selected : slot = id
    · subst slot
      cases output : r.value.2 with
      | none =>
        obtain ⟨final,hfinal,hdead⟩ := dead output
        have eq : pkt = final := Option.some.inj (cell.symm.trans hfinal)
        subst pkt
        cases crypted.symm.trans hdead
      | some out =>
        have source := published out output
        have carrier : OwnerBounds.Carrier r.before := safe.2.2 (.rx (.decrypt id r)) (by
          rw [position]; simp)
        obtain ⟨_,final,_,hf,_,_,bound⟩ := published_below carrier source
        have eq : final = after := Option.some.inj (hf.symm.trans ha)
        subst final
        have cert := OwnerChecks.Safe.published safe position source
        have actual := cert.live.2.2.1
        have eq : pkt = {out with state := .crypted} := Option.some.inj (cell.symm.trans actual)
        subst pkt
        change out.peer < after.nextPeer
        rw [cert.live.packet_peer]
        exact bound
    · have packet := congrFun (congrArg (fun s => s.2.1) frame) slot
      have old : (w.wg.dev.bind fun d => d.rxSkbs[slot]?) = some pkt := by
        simpa [PublicationHistory.around,selected,RxDisposition.nativeRxStore,ha,hp] using packet.symm
      obtain ⟨before,hb,oldPacket⟩ := Option.bind_eq_some_iff.mp old
      have fields : (after.ifindex,after.nextPeer) = (before.ifindex,before.nextPeer) := by
        simpa [frontier,ha,hb] using prepare_frontier w v h t (some pid) hr
      have monotone := FrontiersLe.of_eq (prepare_frontier w v h t (some pid) hr)
      exact Nat.lt_of_lt_of_le (packets before hb slot pkt oldPacket crypted)
        (monotone before after hb ha (congrArg Prod.fst fields).symm)

/-- Stop retains only the checked prefix; normal endpoints retain both the
publication anchor and its concrete peer bound. -/
theorem prepare_preserves :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg)
      OwnerChecks.Safe Origins.HistoryAdapters.prepare := by
  intro w h hi
  obtain ⟨suffix,appends,safe,post⟩ := OwnerPrepare.prepare w h hi.1
  refine ⟨suffix,appends,safe,?_⟩
  cases run : runPrefix Origins.HistoryAdapters.prepare w h with
  | mk result journal =>
    cases result with
    | error stop => trivial
    | ok out =>
      rcases out with ⟨value,v⟩
      simp only [run] at post ⊢
      exact ⟨post,PublicationHistory.prepare_normal w v h journal value hi.1 hi.2.1 run,
        prepare_below w v h journal value hi.1 hi.2.2 run⟩

end Leanux.Proofs.WG.PublicationFrontier
