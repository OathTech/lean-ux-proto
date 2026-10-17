import Leanux.Proofs.WG.Queues.JointPrimitives
import Leanux.Proofs.WG.Configuration.PeerTailRouting
import Leanux.Proofs.WG.Lifetimes.ConfigurationPeer

/-! The existing allowed-IP control sequence interpreted in the joint journal.
The routing projection keeps each completed mutation before cleanup; the RX
projection keeps the actual lifetime observations and every incoming RX event. -/
namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps Configuration

private theorem project_pure {E F α : Type} (ρ : E → Option F) (x : α) :
    StateProjectsPrefix ρ id (pure x : WGPrefix E α) (pure x) := fun _ _ _ => rfl

private theorem project_lift {E F α : Type} (ρ : E → Option F) (a : WG.M α) :
    StateProjectsPrefix ρ id (liftWGPrefix a) (liftWGPrefix a) := by
  intro w ambient h
  change ((a.run w).run ambient, h.filterMap ρ) =
    (((a.run w).run ambient).map (fun ((x,v),t) => ((x,v),t)), h.filterMap ρ)
  cases (a.run w).run ambient <;> rfl

private theorem project_forIn {E F α β : Type} (ρ : E → Option F)
    (xs : List α) (initial : β)
    (g : α → β → WGPrefix E (ForInStep β))
    (a : α → β → WGPrefix F (ForInStep β))
    (hg : ∀ x b, StateProjectsPrefix ρ id (g x b) (a x b)) :
    StateProjectsPrefix ρ id (forIn xs initial g) (forIn xs initial a) := by
  induction xs generalizing initial with
  | nil => exact project_pure ρ initial
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply StateProjectsPrefix.bind ρ id id (hg x initial)
    intro step
    cases step with
    | done b => exact project_pure ρ b
    | yield b => exact ih b

/-- Composition does not assume journal independence or restrict the incoming
histories. The continuation receives the actual projected prefix on both sides. -/
theorem peerAllowedIpsWith_projects {E F : Type} (ρ : E → Option F)
    (record : Decision → Bool → WGPrefix E Bool)
    (record' : Decision → Bool → WGPrefix F Bool)
    (allowed : AllowedIpAttrs → WGPrefix E Int)
    (allowed' : AllowedIpAttrs → WGPrefix F Int)
    (out : Int → WGPrefix E Int) (out' : Int → WGPrefix F Int)
    (next : Int → WGPrefix E Int) (next' : Int → WGPrefix F Int)
    (hr : ∀ d b, StateProjectsPrefix ρ id (record d b) (record' d b))
    (ha : ∀ ip, StateProjectsPrefix ρ id (allowed ip) (allowed' ip))
    (ho : ∀ ret, StateProjectsPrefix ρ id (out ret) (out' ret))
    (hn : ∀ ret, StateProjectsPrefix ρ id (next ret) (next' ret)) (attrs : PeerAttrs) :
    StateProjectsPrefix ρ id (peerAllowedIpsWith record allowed out attrs next)
      (peerAllowedIpsWith record' allowed' out' attrs next') := by
  unfold peerAllowedIpsWith
  apply StateProjectsPrefix.bind ρ id id (hr _ _)
  intro has
  cases has with
  | false => simpa only [id_eq, Bool.false_eq_true, ite_false] using hn 0
  | true =>
    simp only [id_eq, ite_true]
    apply StateProjectsPrefix.bind ρ id id
    · apply project_forIn ρ
      intro entry acc
      apply StateProjectsPrefix.bind ρ id id (hr _ _)
      intro _
      cases entry with
      | malformed =>
        apply StateProjectsPrefix.bind ρ id id (hr _ _)
        intro _
        apply StateProjectsPrefix.bind ρ id id (ho _)
        intro result
        exact project_pure ρ _
      | attrs ip =>
        apply StateProjectsPrefix.bind ρ id id (hr _ _)
        intro _
        apply StateProjectsPrefix.bind ρ id id (ha ip)
        intro ret
        apply StateProjectsPrefix.bind ρ id id (hr _ _)
        intro bad
        cases bad with
        | false => exact project_pure ρ _
        | true =>
          apply StateProjectsPrefix.bind ρ id id (ho _)
          intro result
          exact project_pure ρ _
    · intro acc
      rcases acc with ⟨early,ret⟩
      cases early with
      | some result => exact project_pure ρ _
      | none =>
        apply StateProjectsPrefix.bind ρ id id (hr _ _)
        intro _
        exact hn ret

private theorem project_erases_frame {E F α : Type} (ρ : E → Option F)
    {g : WGPrefix E α} {a : WG.M α}
    (he : ErasesStatePrefix g a) (hh : StateHistoryFrame ρ g) :
    StateProjectsPrefix ρ id g (liftWGPrefix a : WGPrefix F α) := by
  intro w ambient h
  have he' := he w ambient h
  have hh' := hh w ambient h
  change (runWGPrefix g w ambient h).1 = (a.run w).run ambient at he'
  change (runWGPrefix g w ambient h).2.filterMap ρ = h.filterMap ρ at hh'
  change ((a.run w).run ambient,h.filterMap ρ) =
    ((runWGPrefix g w ambient h).1.map (fun ((x,v),t) => ((x,v),t)),
      (runWGPrefix g w ambient h).2.filterMap ρ)
  rw [hh',he']
  cases (a.run w).run ambient <;> rfl

def peerConfigOut (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) : WGPrefix Event Int :=
  access (peerConfigOutPrefix attrs peer ret)

theorem peerConfigOut_routing (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateProjectsPrefix routingEvent id (peerConfigOut attrs peer ret)
      (peerConfigOutObserved attrs peer ret) := by
  have he : ErasesStatePrefix (peerConfigOutPrefix attrs peer ret)
      (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret) := by
    unfold peerConfigOutPrefix
    exact erasesStatePrefix_bind (peerPutMixed_erases _) (fun _ =>
      erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _))
  have h := project_erases_frame routingEvent (access_erases he)
    (access_routing (peerConfigOutPrefix attrs peer ret))
  have heq : liftWGPrefix
      (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret) =
      peerConfigOutObserved attrs peer ret := by
    funext w ambient
    apply ExceptT.ext
    funext history
    change runStatePrefix (liftWGPrefix _) w ambient history =
      runStatePrefix (peerConfigOutObserved attrs peer ret) w ambient history
    unfold peerConfigOutObserved liftWGPrefix
    rw [runStatePrefix_lift, runStatePrefix_bind, runStatePrefix_lift]
    simp only [StateT.run_bind]
    cases hp : ((peerPut peer).run w).run ambient with
    | error e => rfl
    | ok result =>
      rcases result with ⟨⟨u,v⟩,ambient'⟩
      cases u
      simp only [bind, Except.bind]
      change _ = runStatePrefix (liftStatePrefix (branch .peerZeroPsk attrs.presharedKey.isSome : WG.M Bool) >>= fun _ => pure ret) v ambient' history
      rw [runStatePrefix_bind, runStatePrefix_lift]
      cases hb : ((branch .peerZeroPsk attrs.presharedKey.isSome : WG.M Bool).run v).run ambient' <;> rfl
  simpa only [peerConfigOut,heq] using h

def peerAllowedIps (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix Event Int) : WGPrefix Event Int :=
  peerAllowedIpsWith (fun d b => liftWGPrefix (branch d b))
    (completedAllowedip pid) (peerConfigOut attrs peer) attrs next

theorem peerAllowedIps_routing (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix Event Int) (routingNext : Int → WGPrefix RoutingCompletion Int)
    (hn : ∀ ret, StateProjectsPrefix routingEvent id (next ret) (routingNext ret)) :
    StateProjectsPrefix routingEvent id (peerAllowedIps attrs peer pid next)
      (peerAllowedIpsObservedWG attrs peer pid routingNext) := by
  exact peerAllowedIpsWith_projects routingEvent _ _ _ _ _ _ _ _
    (fun d b => project_lift routingEvent (branch d b))
    (completedAllowedip_routing pid) (peerConfigOut_routing attrs peer) hn attrs

/-- The RX interpretation uses the existing native lifetime focus at every
primitive. Whole-tail focus equality is a separate append/composition fact. -/
def peerAllowedIpsRx (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix RxHistory.Event Int) : WGPrefix RxHistory.Event Int :=
  peerAllowedIpsWith (fun d b => liftWGPrefix (branch d b))
    (fun ip => nativeRx (setAllowedipPrefix pid ip))
    (fun ret => nativeRx (peerConfigOutPrefix attrs peer ret)) attrs next

theorem peerAllowedIps_rx (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix Event Int) (rxNext : Int → WGPrefix RxHistory.Event Int)
    (hn : ∀ ret, StateProjectsPrefix rxEvent id (next ret) (rxNext ret)) :
    StateProjectsPrefix rxEvent id (peerAllowedIps attrs peer pid next)
      (peerAllowedIpsRx attrs peer pid rxNext) := by
  exact peerAllowedIpsWith_projects rxEvent _ _ _ _ _ _ _ _
    (fun d b => project_lift rxEvent (branch d b))
    (fun ip => completed_rx (setAllowedipPrefix pid ip) (.allowedIp pid ip))
    (fun ret => access_rx (peerConfigOutPrefix attrs peer ret)) hn attrs

/-- An append-preserving lower action and its exact focused interpretation. -/
private def Focused {E F α : Type} (encode : E → F) (decode : F → Option E)
    (g : WGPrefix F α) (a : WGPrefix E α) : Prop :=
  StateAppends a ∧ g = focusStatePrefix encode decode a

private theorem focused_pure {E F α : Type} (encode : E → F) (decode : F → Option E)
    (x : α) : Focused encode decode (pure x) (pure x) := by
  refine ⟨StateAppends.pure x, ?_⟩
  funext w ambient
  apply ExceptT.ext
  funext h
  change (Except.ok (ε := Stop) ((x,w),ambient),h) =
    (Except.ok (ε := Stop) ((x,w),ambient),h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

private theorem focused_lift {E F α : Type} (encode : E → F) (decode : F → Option E)
    (a : WG.M α) : Focused encode decode (liftWGPrefix a) (liftWGPrefix a) := by
  refine ⟨StateAppends.lift a, ?_⟩
  funext w ambient
  apply ExceptT.ext
  funext h
  change (((a.run w).run ambient),h) =
    (((a.run w).run ambient),h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

private theorem focused_bind {E F α β : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e)
    {g : WGPrefix F α} {a : WGPrefix E α}
    {f : α → WGPrefix F β} {b : α → WGPrefix E β}
    (hg : Focused encode decode g a) (hf : ∀ x, Focused encode decode (f x) (b x)) :
    Focused encode decode (g >>= f) (a >>= b) := by
  refine ⟨hg.1.bind (fun x => (hf x).1), ?_⟩
  rw [hg.2]
  have he : f = fun x => focusStatePrefix encode decode (b x) := funext fun x => (hf x).2
  rw [he]
  funext w ambient
  apply ExceptT.ext
  funext h
  exact focusPrefix_bind_appends encode decode hd (hg.1 w)
    (fun out => (hf out.1).1 out.2) ambient h

private theorem focused_forIn {E F α β : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e) (xs : List α) (initial : β)
    (g : α → β → WGPrefix F (ForInStep β)) (a : α → β → WGPrefix E (ForInStep β))
    (hg : ∀ x b, Focused encode decode (g x b) (a x b)) :
    Focused encode decode (forIn xs initial g) (forIn xs initial a) := by
  induction xs generalizing initial with
  | nil => exact focused_pure encode decode initial
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply focused_bind encode decode hd (hg x initial)
    intro step
    cases step with
    | done b => exact focused_pure encode decode b
    | yield b => exact ih b

private theorem allowedIps_focused {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e)
    (record : Decision → Bool → WGPrefix F Bool)
    (record' : Decision → Bool → WGPrefix E Bool)
    (allowed : AllowedIpAttrs → WGPrefix F Int)
    (allowed' : AllowedIpAttrs → WGPrefix E Int)
    (out : Int → WGPrefix F Int) (out' : Int → WGPrefix E Int)
    (next : Int → WGPrefix F Int) (next' : Int → WGPrefix E Int)
    (hr : ∀ d b, Focused encode decode (record d b) (record' d b))
    (ha : ∀ ip, Focused encode decode (allowed ip) (allowed' ip))
    (ho : ∀ ret, Focused encode decode (out ret) (out' ret))
    (hn : ∀ ret, Focused encode decode (next ret) (next' ret)) (attrs : PeerAttrs) :
    Focused encode decode (peerAllowedIpsWith record allowed out attrs next)
      (peerAllowedIpsWith record' allowed' out' attrs next') := by
  unfold peerAllowedIpsWith
  apply focused_bind encode decode hd (hr _ _)
  intro has
  cases has with
  | false => exact hn 0
  | true =>
    apply focused_bind encode decode hd
    · apply focused_forIn encode decode hd
      intro entry acc
      apply focused_bind encode decode hd (hr _ _)
      intro _
      cases entry with
      | malformed =>
        apply focused_bind encode decode hd (hr _ _)
        intro _
        apply focused_bind encode decode hd (ho _)
        intro result
        exact focused_pure encode decode _
      | attrs ip =>
        apply focused_bind encode decode hd (hr _ _)
        intro _
        apply focused_bind encode decode hd (ha ip)
        intro ret
        apply focused_bind encode decode hd (hr _ _)
        intro bad
        cases bad with
        | false => exact focused_pure encode decode _
        | true =>
          apply focused_bind encode decode hd (ho _)
          intro result
          exact focused_pure encode decode _
    · intro acc
      rcases acc with ⟨early,ret⟩
      cases early with
      | some result => exact focused_pure encode decode _
      | none =>
        apply focused_bind encode decode hd (hr _ _)
        intro _
        exact hn ret

/-- Exact whole-loop focus, conditional only on the supplied lower actions
actually appending to their journals, on success and on Stop alike. -/
theorem peerAllowedIpsWith_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e)
    (record : Decision → Bool → WGPrefix E Bool) (allowed : AllowedIpAttrs → WGPrefix E Int)
    (out next : Int → WGPrefix E Int)
    (hr : ∀ d b, StateAppends (record d b)) (ha : ∀ ip, StateAppends (allowed ip))
    (ho : ∀ ret, StateAppends (out ret)) (hn : ∀ ret, StateAppends (next ret))
    (attrs : PeerAttrs) :
    peerAllowedIpsWith (fun d b => focusStatePrefix encode decode (record d b))
      (fun ip => focusStatePrefix encode decode (allowed ip))
      (fun ret => focusStatePrefix encode decode (out ret)) attrs
      (fun ret => focusStatePrefix encode decode (next ret)) =
      focusStatePrefix encode decode (peerAllowedIpsWith record allowed out attrs next) :=
  (allowedIps_focused encode decode hd _ _ _ _ _ _ _ _
    (fun d b => ⟨hr d b,rfl⟩) (fun ip => ⟨ha ip,rfl⟩)
    (fun ret => ⟨ho ret,rfl⟩) (fun ret => ⟨hn ret,rfl⟩) attrs).2

private theorem peerPut_appends (peer : Option PeerId) : StateAppends (peerPutMixed peer) :=
  StateAppends.focus _ _ _

private theorem listAdd_appends (pid : PeerId) (id : NodeId) :
    StateAppends (listAddTailPrefix pid id) :=
  (StateAppends.focus _ _ _).bind (fun _ => StateAppends.focus _ _ _)

private theorem listDelEntries_appends (id : NodeId) (xs : List (PeerId × Peer)) :
    StateAppends (listDelEntriesPrefix id xs) := by
  induction xs with
  | nil => exact StateAppends.pure ()
  | cons item xs ih =>
    rcases item with ⟨pid,p⟩
    unfold listDelEntriesPrefix
    have read : StateAppends (savedPeerRead pid p) := fun _ _ _ => ⟨[.peer (.read pid p.internalId)],rfl⟩
    apply read.bind
    intro _
    dsimp only
    split
    · exact (StateAppends.focus _ _ _).bind (fun _ => ih)
    · exact ih

private theorem listDel_appends (id : NodeId) : StateAppends (listDelPrefix id) :=
  (StateAppends.lift getDev).bind (fun d => listDelEntries_appends id d.peers.toList)

private theorem appends_ite {α : Type} (p : Prop) [Decidable p] {a b : MixedM α}
    (ha : p → StateAppends a) (hb : ¬p → StateAppends b) :
    StateAppends (if p then a else b) := by
  by_cases h : p
  · simpa only [h,ite_true] using ha h
  · simpa only [h,ite_false] using hb h

private theorem add_appends (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    StateAppends (addAllowedIpPrefix root bits key cidr peer) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have pure' {α : Type} (x : α) : StateAppends (pure x : MixedM α) := StateAppends.pure x
  unfold addAllowedIpPrefix
  repeat' first
    | with_reducible exact listAdd_appends _ _
    | with_reducible exact listDel_appends _
    | with_reducible exact lifted _
    | with_reducible exact pure' _
    | with_reducible apply StateAppends.bind
    | with_reducible apply appends_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem insert_appends (family addr cidr : Nat) (pid : PeerId) :
    StateAppends (insertAllowedIpPrefix family addr cidr pid) := by
  unfold insertAllowedIpPrefix
  apply (StateAppends.lift _).bind
  intro _
  split <;> exact add_appends _ _ _ _ _

private theorem allowed_appends (pid : PeerId) (ip : AllowedIpAttrs) :
    StateAppends (setAllowedipPrefix pid ip) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have pure' {α : Type} (x : α) : StateAppends (pure x : MixedM α) := StateAppends.pure x
  unfold setAllowedipPrefix
  repeat' first
    | with_reducible exact insert_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact pure' _
    | with_reducible apply StateAppends.bind
    | with_reducible apply appends_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem out_appends (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateAppends (peerConfigOutPrefix attrs peer ret) :=
  (peerPut_appends peer).bind (fun _ => (StateAppends.lift _).bind (fun _ => StateAppends.pure ret))

/-- The RX interpretation is the unchanged focus of the original lifetime
loop. Only the supplied continuation needs an append contract; the concrete
configuration actions establish their own unconditional append behavior. -/
theorem peerAllowedIpsRx_eq (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → MixedM Int) (hn : ∀ ret, StateAppends (next ret)) :
    peerAllowedIpsRx attrs peer pid (fun ret => nativeRx (next ret)) =
      nativeRx (peerAllowedIpsPrefix attrs peer pid next) := by
  have inner := allowedIps_focused AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    (fun d b => liftWGPrefix (branch d b)) (fun d b => liftWGPrefix (branch d b))
    (fun ip => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setAllowedipPrefix pid ip))
    (setAllowedipPrefix pid)
    (fun ret => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerConfigOutPrefix attrs peer ret))
    (peerConfigOutPrefix attrs peer)
    (fun ret => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (next ret)) next
    (fun d b => focused_lift _ _ (branch d b))
    (fun ip => ⟨allowed_appends pid ip,rfl⟩)
    (fun ret => ⟨out_appends attrs peer ret,rfl⟩) (fun ret => ⟨hn ret,rfl⟩) attrs
  have outer := allowedIps_focused RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (fun d b => liftWGPrefix (branch d b)) (fun d b => liftWGPrefix (branch d b))
    (fun ip => nativeRx (setAllowedipPrefix pid ip))
    (fun ip => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setAllowedipPrefix pid ip))
    (fun ret => nativeRx (peerConfigOutPrefix attrs peer ret))
    (fun ret => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerConfigOutPrefix attrs peer ret))
    (fun ret => nativeRx (next ret))
    (fun ret => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (next ret))
    (fun d b => focused_lift _ _ (branch d b))
    (fun _ => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun _ => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun _ => ⟨StateAppends.focus _ _ _,rfl⟩) attrs
  exact outer.2.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner.2)

theorem peerAllowedIps_rx_existing (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix Event Int) (rxNext : Int → MixedM Int)
    (ha : ∀ ret, StateAppends (rxNext ret))
    (hn : ∀ ret, StateProjectsPrefix rxEvent id (next ret) (nativeRx (rxNext ret))) :
    StateProjectsPrefix rxEvent id (peerAllowedIps attrs peer pid next)
      (nativeRx (peerAllowedIpsPrefix attrs peer pid rxNext)) := by
  rw [← peerAllowedIpsRx_eq attrs peer pid rxNext ha]
  exact peerAllowedIps_rx attrs peer pid next _ hn

theorem peerAllowedIps_rx_product (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix Event Int) (rxNext : Int → MixedM Int)
    (ha : ∀ ret, StateAppends (rxNext ret))
    (hn : ∀ ret, StateProjectsPrefix rxEvent id (next ret) (nativeRx (rxNext ret))) :
    ProjectsPrefix rxEvent id (liftWGObserver (peerAllowedIps attrs peer pid next))
      (RxHistory.mixed (liftWGObserver (peerAllowedIpsPrefix attrs peer pid rxNext))) := by
  rw [← nativeRx_product]
  exact (peerAllowedIps_rx_existing attrs peer pid next rxNext ha hn).liftWGObserver _ _

end Leanux.Proofs.WG.Queues.RoutingJoint
