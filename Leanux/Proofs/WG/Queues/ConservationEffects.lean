import Leanux.Proofs.WG.Queues.ConservationSyscall
import Leanux.Proofs.WG.Queues.TrafficOccurrences

/-! Consequences of the concrete source certificates. Earlier carriers remain
pending or occur in the exact fresh removal suffix. These are source-only
conclusions; newly accepted occurrences and named dispositions are separate. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConservationEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open ConservationSource

def Conserves {action : RxHistory.Obs α} (rule : Rule action) : Prop :=
  ∀ {cs w h x v k next}, rule.relation cs w h x v k next →
    TrafficEffects.Conserved cs next h k

theorem unchanged {action : RxHistory.Obs α} (rule : Rule action)
    (same : ∀ {cs w h x v k next},rule.relation cs w h x v k next→next=cs) :
    Conserves rule := by
  intro cs w h x v k next certificate
  obtain ⟨suffix,hist⟩ := rule.appends certificate
  exact ⟨suffix,hist,fun c member=>Or.inl (same certificate ▸ member)⟩

theorem pure (x : α) : Conserves (ConservationSource.pure x) :=
  unchanged (ConservationSource.pure x) (fun certificate=>certificate.2.2.2)

theorem bind {action : RxHistory.Obs α} {nextAction : α→RxHistory.Obs β}
    {first : Rule action} {next : ∀x,Rule (nextAction x)}
    (front : Conserves first) (tail : ∀x,Conserves (next x)) :
    Conserves (ConservationSource.bind first next) := by
  rintro cs w h y v k final ⟨x,u,j,middle,a,b⟩
  exact TrafficEffects.trans (front a) (tail x b)

theorem lift (action : Leanux.M α) : Conserves (HolderTrafficDispatch.lift action) :=
  unchanged (HolderTrafficDispatch.lift action) (fun certificate=>certificate.2.2)

theorem audit (action : AuditM α) : Conserves (ConservationSyscall.audit action) :=
  unchanged (ConservationSyscall.audit action) (fun certificate=>certificate.2)

theorem deferred (action : RxHistory.Obs α) : Conserves (ConservationSyscall.deferred action) := by
  rintro cs w h x v k next ⟨_,suffix,hist,rfl⟩
  exact TrafficEffects.removal hist

theorem branch (condition : Bool) {yes no : RxHistory.Obs α}
    {a : Rule yes} {b : Rule no} (ha : Conserves a) (hb : Conserves b) :
    Conserves (HolderTrafficDispatch.branch condition a b) := by
  cases condition
  · exact hb
  · exact ha

theorem receive (msg : List UInt8) (src : SkbSource) : Conserves (ConservationSource.receive msg src) :=
  fun certificate=>TrafficEffects.receive certificate.2

theorem poll (pid : PeerId) (budget : Nat) : Conserves (ConservationSource.poll pid budget) := by
  rintro cs w h x v k next ⟨_,suffix,hist,rfl⟩
  exact TrafficEffects.removal hist

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Conserves (ConservationSource.inject family port msg tos ll dest) := TrafficEffects.inject

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Conserves (ConservationSource.flood count port family messages) := TrafficEffects.flood

theorem batch (entries : List Env.BatchItem) : Conserves (ConservationSource.batch entries) :=
  TrafficEffects.batch

theorem crypt : Conserves ConservationSource.crypt := by
  rintro cs w h x v k next ⟨_,suffix,hist,rfl⟩
  exact TrafficEffects.removal hist

theorem afterBatch : Conserves ConservationSource.afterBatch := by
  rintro cs w h x v k next ⟨_,suffix,hist,rfl⟩
  exact TrafficEffects.removal hist

theorem idle : Conserves HolderTrafficDispatch.idle := by
  rintro cs w h x v k next ⟨_,suffix,hist,rfl⟩
  exact TrafficEffects.removal hist

theorem socket (fd : Nat) {action : RxHistory.Obs Int} {rule : Rule action}
    (body : Conserves rule) : Conserves (HolderTrafficDispatch.socket fd rule) := by
  apply bind (lift _)
  intro f
  apply branch
  · exact pure _
  · exact bind body (fun ret=>bind (lift _) (fun _=>pure ret))

theorem observe : Conserves HolderTrafficDispatch.observe :=
  bind idle (fun _=>lift _)

theorem injectDispatch (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Conserves (HolderTrafficDispatch.injectDispatch family port msg tos ll dest) :=
  socket _ (inject family port msg tos ll dest)

theorem observeDispatch : Conserves HolderTrafficDispatch.observeDispatch := by
  unfold HolderTrafficDispatch.observeDispatch
  exact bind observe (fun out=>bind (lift _) (fun _=>socket _ (pure out.1)))

theorem checked_pure (x : α) : Conserves (ConservationSyscall.Checked.pure (loans:=loans) x).rule := pure x

theorem checked_bind {action : RxHistory.Obs α} {nextAction : α→RxHistory.Obs β}
    {first : ConservationSyscall.Checked loans action}
    {next : ∀x,ConservationSyscall.Checked loans (nextAction x)}
    (front : Conserves first.rule) (tail : ∀x,Conserves (next x).rule) :
    Conserves (ConservationSyscall.Checked.bind first next).rule := bind front tail

theorem checked_lift (action : Leanux.M α) (frame : SameView (fun w : World=>wgStoreView w.wg) action) :
    Conserves (ConservationSyscall.Checked.lift (loans:=loans) action frame).rule := lift action

theorem checked_audit (action : AuditM α)
    (keeps : ∀cs,PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit action)) :
    Conserves (ConservationSyscall.Checked.audit action keeps).rule := audit action

theorem checked_deferred (action : RxHistory.Obs α)
    (normal : ∀{cs w h x v k},HolderEntry.Inv cs loans h w→
      runPrefix action w h=(.ok (x,v),k)→
      ∃suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :
    Conserves (ConservationSyscall.Checked.deferred action normal).rule := deferred action

theorem checked_branch (condition : Bool) {yes no : RxHistory.Obs α}
    {a : ConservationSyscall.Checked loans yes} {b : ConservationSyscall.Checked loans no}
    (ha : Conserves a.rule) (hb : Conserves b.rule) :
    Conserves (ConservationSyscall.Checked.branch condition a b).rule := branch condition ha hb

theorem checked_transport {action other : RxHistory.Obs α} (same : action=other)
    (checked : ConservationSyscall.Checked loans action) (effect : Conserves checked.rule) :
    Conserves (same ▸ checked).rule := by
  cases same
  exact effect

theorem checked_mpr {action other : RxHistory.Obs α} (same : action=other)
    (types : ConservationSyscall.Checked loans action=ConservationSyscall.Checked loans other)
    (checked : ConservationSyscall.Checked loans other) (effect : Conserves checked.rule) :
    Conserves (Eq.mpr types checked).rule := by
  cases same
  exact effect

theorem checked_forIn (items : List γ) (initial : β)
    (action : γ→β→RxHistory.Obs (ForInStep β))
    (steps : ∀x y,ConservationSyscall.Checked loans (action x y))
    (effect : ∀x y,Conserves (steps x y).rule) :
    Conserves (ConservationSyscall.Checked.forIn items initial action steps).rule := by
  induction items generalizing initial with
  | nil=>exact pure initial
  | cons item rest ih=>
    simp only [ConservationSyscall.Checked.forIn]
    apply checked_mpr (same := List.forIn_cons action item rest initial)
    apply checked_bind (effect item initial)
    intro step
    cases step with
    | done result=>exact pure result
    | yield result=>exact ih result

end Leanux.Proofs.WG.Queues.RxCredits.ConservationEffects
