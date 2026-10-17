import Leanux.Proofs.WG.Packets.PublicationPrepareInvariant
import Leanux.Proofs.WG.Origins.OwnerCreation

/-! A packet-owner frontier is carried on live crypted cells, independently
of later key validity or peer residency. Publication establishes the bound;
same-epoch transport and concrete creation keep it. Runner reachability is
not assumed or asserted. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity
variable {id : SkbId}

/-- Only live crypted packets need this bound. Device absence is vacuous. -/
def PeersBelow (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ (id : SkbId) (pkt : RxPacket), d.rxSkbs[id]? = some pkt →
    pkt.state = .crypted → pkt.peer < d.nextPeer

def frontier (w : WGWorld) := w.dev.map fun d => (d.ifindex,d.nextPeer)

/-- Monotonicity is asserted only within the same device epoch. Reset cases
must discharge the new packet population separately. -/
def FrontiersLe (w v : WGWorld) : Prop :=
  ∀ before after, w.dev = some before → v.dev = some after →
    before.ifindex = after.ifindex → before.nextPeer ≤ after.nextPeer

def Inv (history : List RxHistory.Event) (w : WGWorld) : Prop :=
  PublicationHistory.Inv history w ∧ PeersBelow w

/-- Appending actual later events keeps the strict earlier publication
witness and does not alter the state-local packet frontier. -/
theorem Inv.append (hi : Inv history w) (suffix : List RxHistory.Event) :
    Inv (history ++ suffix) w := ⟨hi.1.append suffix,hi.2⟩

theorem PeersBelow.no_crypted (w : WGWorld)
    (empty : ∀ d, w.dev = some d → ∀ (id : SkbId) (pkt : RxPacket), d.rxSkbs[id]? = some pkt → pkt.state ≠ .crypted) :
    PeersBelow w := fun d hd id pkt hp crypted => False.elim (empty d hd id pkt hp crypted)

theorem initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  refine ⟨PublicationHistory.initial net bare w hw,?_⟩
  have hd := congrArg WGStoreView.dev hw
  change w.dev = (if net && !bare then some {ifindex := 3,ifname := "wg0"} else none) at hd
  apply PeersBelow.no_crypted
  intro d resident id pkt hp
  rw [hd] at resident
  split at resident
  · cases resident
    simp at hp
  · cases resident

theorem PeersBelow.transport (hi : PeersBelow w)
    (packets : RxDisposition.nativeRxStore v = RxDisposition.nativeRxStore w)
    (monotone : FrontiersLe w v) : PeersBelow v := by
  intro after ha id pkt hp crypted
  have old : (w.dev.bind fun d => d.rxSkbs[id]?) = some pkt := by
    simpa [RxDisposition.nativeRxStore,ha,hp] using
      (congrFun (congrArg Prod.snd packets) id).symm
  obtain ⟨before,hb,packet⟩ := Option.bind_eq_some_iff.mp old
  have epoch : before.ifindex = after.ifindex := by
    simpa [RxDisposition.nativeRxStore,ha,hb] using (congrArg Prod.fst packets).symm
  exact Nat.lt_of_lt_of_le (hi before hb id pkt packet crypted)
    (monotone before after hb ha epoch)

theorem FrontiersLe.of_eq (same : frontier v = frontier w) : FrontiersLe w v := by
  intro before after hb ha _
  have fields : (after.ifindex,after.nextPeer) = (before.ifindex,before.nextPeer) := by
    simpa [frontier,ha,hb] using same
  exact Nat.le_of_eq (congrArg Prod.snd fields).symm

/-- The actual getter/decrypt pair retains epoch and allocation frontier,
including the normal key-invalidation arm. -/
theorem readDecrypt_frontier (id : SkbId) : SameView frontier (RxOrigin.readDecrypt id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  simp only [RxOrigin.readDecrypt,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,read,readAmbient,hread,decrypted,after,afterAmbient,run,done⟩ := hr
  obtain ⟨readEq,ambientEq,_,_,_⟩ := Packets.getRxSkb_current id w read pkt a readAmbient hread
  subst read
  subst readAmbient
  cases done
  have full := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.decryptPacket_view) pkt)
    w a decrypted v b run
  simpa only [ConfiguredIdentity.view,ConfiguredIdentity.state,frontier,Option.map_map,Function.comp_def] using
    congrArg (fun s : Option ConfiguredIdentity.State => s.map fun s => (s.epoch,s.frontier)) full

theorem publish_frontier (id : SkbId) (state : PacketState) :
    SameView frontier (RxWorkers.publishSource id state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a pid v b hr
  obtain ⟨d,pkt,key,p,hd,_,_,_,_,effect⟩ := publish_execution id state w v a b pid hr
  have hv := congrArg WGStoreView.dev effect
  change v.dev = some _ at hv
  simp only [frontier,hv,hd,Option.map_some]

/-- A successful publication has the very same device epoch and peer
frontier as its captured decrypt entry. -/
theorem published_frontier (published : Published id r out pid v b) :
    frontier v = frontier r.before := by
  obtain ⟨valid,output,checked,a,installed,c,hbranch,hstore,hpublish⟩ := published
  have read := (ProjectedAction.iff_run_ambient _ _ _).mp (readDecrypt_frontier id)
    r.before r.ambientBefore r.value r.after r.ambientAfter valid
  have branchFrame := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .decWorkerDecrypted true)
      (fun w => frontier w = frontier r.after))
    r.after r.ambientAfter true checked a rfl hbranch
  have store : Hoare (setRxSkb id (fun _ => out))
      (fun w => frontier w = frontier checked) (fun _ w => frontier w = frontier checked) := by
    unfold setRxSkb
    apply hoare_liftSkb
    intro w d packets hi hd
    simpa only [frontier,hd,Option.map_some] using hi
  have stored := (hoare_iff_run_ambient _ _ _).mp store checked a () installed c rfl hstore
  have final := (ProjectedAction.iff_run_ambient _ _ _).mp (publish_frontier id .crypted)
    installed c pid v b hpublish
  exact final.trans (stored.trans (branchFrame.trans read))

/-- The bound is derived at the actual publication, using the checked
receiving owner at the captured entry. Cleared/invalid later keys are irrelevant. -/
theorem published_below (carrier : OwnerBounds.Carrier r.before)
    (published : Published id r out pid v b) :
    ∃ before after, r.before.dev = some before ∧ v.dev = some after ∧
      after.ifindex = before.ifindex ∧ after.nextPeer = before.nextPeer ∧ pid < after.nextPeer := by
  obtain ⟨before,key,p,after,hb,packet,hkey,word,resident,ha,epoch,_⟩ :=
    published_peer id r out pid v b published
  obtain ⟨decryptDev,decryptKey,hd,_,hk,valid,_,_,_⟩ :=
    RxOrigin.decrypt_receipt id r out published.1 published.2.1
  have same : decryptDev = before := Option.some.inj (hd.symm.trans hb)
  subst decryptDev
  have same : decryptKey = key := Option.some.inj (hk.symm.trans hkey)
  subst decryptKey
  have bound := carrier.owners before hb r.value.1.keypair key hkey valid pid word
  have fields : (after.ifindex,after.nextPeer) = (before.ifindex,before.nextPeer) := by
    simpa [frontier,ha,hb] using published_frontier published
  refine ⟨before,after,hb,ha,epoch,congrArg Prod.snd fields,?_⟩
  change pid < after.nextPeer
  have next : after.nextPeer = before.nextPeer := congrArg Prod.snd fields
  rw [next]
  exact bound

end Leanux.Proofs.WG.PublicationFrontier
