import Leanux.Proofs.WG.Packets.PublicationPrepareFrames

/-! The original prepare observer preserves every live-packet anchor, creates
its selected anchor after actual successful decryption, and preserves the
existing safe journal on Stop. No initialized whole-run claim is made. -/
namespace Leanux.Proofs.WG.PublicationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity
open Origins.HistorySupport (rxEncode rxDecode)

/-- The double focus retains every old RX event, promotes exactly the new
native suffix, and writes back only the actual WG/Ambient endpoints. -/
theorem prepare_run (w : World) (h : List RxHistory.Event) :
    runPrefix Origins.HistoryAdapters.prepare w h =
      let result := runWGPrefix RxOrigin.prepare w.wg w.ambient (h.filterMap rxDecode)
      (result.1.map (fun ((x,g),a) => (x,{w with wg := g,ambient := a})),
        h ++ (result.2.drop (h.filterMap rxDecode).length).map rxEncode) := by
  unfold Origins.HistoryAdapters.prepare Origins.HistoryAdapters.focus Origins.HistoryAdapters.localPrepare
  rw [Origins.HistorySupport.focus_compose]
  rfl

/-- Product focusing retains the concrete native packet frame together with
the exact newly promoted occurrence. -/
theorem prepare_packet_cases (w v : World) (h t : List RxHistory.Event) (pid : PeerId)
    (hr : runPrefix Origins.HistoryAdapters.prepare w h = (.ok (some pid,v),t)) :
    ∃ id, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ pre tail,
      r.Valid (RxOrigin.readDecrypt id) ∧
      t = h ++ pre ++ .rx (.decrypt id r) :: tail ∧
      around id v.wg = around id w.wg ∧
      (r.value.2 = none → ∃ pkt, (RxDisposition.nativeRxStore v.wg).2 id = some pkt ∧ pkt.state = .dead) ∧
      (∀ out, r.value.2 = some out → Published id r out pid v.wg v.ambient) := by
  rw [prepare_run] at hr
  cases native : runWGPrefix RxOrigin.prepare w.wg w.ambient (h.filterMap rxDecode) with
  | mk result journal =>
    simp only [native] at hr
    cases result with
    | error stop => cases hr
    | ok endpoint =>
      rcases endpoint with ⟨⟨value,g⟩,ambient⟩
      simp only [Except.map,Except.ok.injEq,Prod.mk.injEq] at hr
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := hr
      obtain ⟨id,r,pre,tail,valid,position,frame,dead,published⟩ :=
        native_prepare_selected w.wg g w.ambient ambient (h.filterMap rxDecode) journal pid native
      refine ⟨id,r,pre.map rxEncode,tail.map rxEncode,valid,?_,frame,dead,published⟩
      rw [position]
      simp only [List.append_assoc,List.drop_left,List.map_append,List.map_cons]
      rfl

theorem prepare_none (w v : World) (h t : List RxHistory.Event)
    (hr : runPrefix Origins.HistoryAdapters.prepare w h = (.ok (none,v),t)) : v.wg = w.wg ∧ t = h := by
  rw [prepare_run] at hr
  cases native : runWGPrefix RxOrigin.prepare w.wg w.ambient (h.filterMap rxDecode) with
  | mk result journal =>
    simp only [native] at hr
    cases result with
    | error stop => cases hr
    | ok endpoint =>
      rcases endpoint with ⟨⟨value,g⟩,ambient⟩
      simp only [Except.map,Except.ok.injEq,Prod.mk.injEq] at hr
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := hr
      obtain ⟨rfl,rfl⟩ := native_prepare_none w.wg g w.ambient ambient (h.filterMap rxDecode) journal native
      exact ⟨rfl,by simp⟩

/-- All live crypted cells at the actual normal endpoint have certificates.
The decrypt-failure arm is retained and publishes DEAD at its selected cell. -/
theorem prepare_normal (w v : World) (h t : List RxHistory.Event) (result : Option PeerId)
    (owner : OwnerChecks.Inv h w) (packets : Inv h w.wg)
    (hr : runPrefix Origins.HistoryAdapters.prepare w h = (.ok (result,v),t)) : Inv t v.wg := by
  have safe := (OwnerPrepare.prepare w h owner).choose_spec.2.1
  rw [hr] at safe
  cases result with
  | none =>
    obtain ⟨same,rfl⟩ := prepare_none w v h t hr
    rw [same]
    exact packets
  | some pid =>
    obtain ⟨id,r,pre,tail,valid,position,frame,dead,published⟩ := prepare_packet_cases w v h t pid hr
    intro slot pkt cell crypted
    by_cases selected : slot = id
    · subst slot
      cases output : r.value.2 with
      | none =>
        obtain ⟨final,hfinal,hdead⟩ := dead output
        have eq : pkt = final := Option.some.inj (cell.symm.trans hfinal)
        subst pkt
        cases crypted.symm.trans hdead
      | some out => exact anchored_publication safe position (published out output)
    · have packet := congrFun (congrArg (fun s => s.2.1) frame) slot
      have old : (RxDisposition.nativeRxStore w.wg).2 slot = some pkt := by
        simpa only [around,selected,ite_false,cell] using packet.symm
      have anchor := (packets slot pkt old crypted).around selected frame
      rw [position,List.append_assoc]
      exact anchor.append (pre ++ .rx (.decrypt id r) :: tail)

/-- Composition uses the same existing observer and exact failed journal.
A stopped execution receives no fictitious final WG state. -/
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
      exact ⟨post,prepare_normal w v h journal value hi.1 hi.2 run⟩

end Leanux.Proofs.WG.PublicationHistory
