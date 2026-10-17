import Leanux.Proofs.WG.Queues.RxCleanupProtection

/-! Actual index-acquired peer loans and RX admission cuts. The successful
fresh store-back supplies the key's owner word locally. No initialized
ownership, cryptographic affiliation or retrospective reference slack is used. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
set_option pp.structureInstances false

def creditWorld (w : WGWorld) (d : Device) (pid : PeerId) (p : Peer) : WGWorld :=
  {w with dev := some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}}}

/-- The actual get adds one credit; the fresh owner setter may change its word
but preserves peer identity/count/queues and every resident RX cell. -/
def Loan (before : WGWorld) (result : Option PeerId) (after : WGWorld) : Prop :=
  match result with
  | none => peerView after = peerView before ∧ rxView after = rxView before
  | some pid => ∃ d p, before.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      peerView after = peerView (creditWorld before d pid p) ∧
      rxView after = rxView before

theorem ownerStore_credit_frame (owner : IndexOwner) (word : Option PeerId) :
    SameView (fun w => (peerView w,rxView w)) (owner.setPeerWord word) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hr
  cases owner with
  | handshake id =>
    unfold IndexOwner.setPeerWord at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨p,a,readAmbient,hg,hs⟩ := hr
    obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal id w a p ambient readAmbient hg
    cases hs
    simp only [peerView,rxView,hd,Option.map_some,Option.bind_some]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext q
        by_cases h : id = q
        · subst q
          simp [hp]
        · simp [Std.TreeMap.getElem?_insert,h]
    · rfl
  | keypair id =>
    have hu : u = () := by cases u; rfl
    subst u
    obtain ⟨d,k,hd,hk,rfl,_⟩ := Origins.keypair_word_store id word w v ambient ambient' hr
    simp [peerView,rxView,CounterWindow.store,hd]

theorem acquireOwner_loan (owner : IndexOwner) (w v : WGWorld) (result : Option PeerId)
    (ambient ambient' : Ambient)
    (hr : ((Affiliation.acquireOwner owner).run w).run ambient = .ok ((result,v),ambient')) :
    Loan w result v := by
  obtain ⟨word,a,b,readAmbient,borrowedAmbient,hread,hget,hstore⟩ :=
    Affiliation.acquireOwner_acquisition owner w v result ambient ambient' hr
  have ha : a = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves owner (fun z => z = w)) w ambient word a readAmbient rfl hread
  subst a
  have hb := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec word (wgStoreView w)) w readAmbient result b borrowedAmbient rfl hget
  have hs := Prod.mk.inj ((ProjectedAction.iff_run_ambient _ _ _).mp
    (ownerStore_credit_frame owner result) b borrowedAmbient () v ambient' hstore)
  cases result with
  | none =>
    have he := congrArg WGStoreView.dev hb.2
    change b.dev = w.dev at he
    exact ⟨hs.1.trans (by simp only [peerView,he]),hs.2.trans (by simp only [rxView,he])⟩
  | some pid =>
    obtain ⟨d,p,hd,hp,hpos,he⟩ := hb.2
    have hedev := congrArg WGStoreView.dev he
    change b.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at hedev
    change w.dev = some d at hd
    refine ⟨d,p,hd,hp,hpos,?_,?_⟩
    · exact hs.1.trans (by simp only [peerView,creditWorld,hedev])
    · exact hs.2.trans (by simp only [rxView,hedev,hd,Option.map_some,Option.bind_some])

theorem acquireOwner_loan_spec (owner : IndexOwner) (initial : WGWorld) :
    ⦃fun w => ⌜wgStoreView w = wgStoreView initial⌝⦄ Affiliation.acquireOwner owner
    ⦃⇓? result w => ⌜Loan initial result w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hk hr
  have h := acquireOwner_loan owner w v result ambient ambient' hr
  have hd := congrArg WGStoreView.dev hk
  change w.dev = initial.dev at hd
  cases result <;> simpa [Loan,peerView,rxView,creditWorld,hd] using h

/-- Complete literal index scan: its returned peer carries exactly the source
loan, including the ordinary None arm after a failed nullable acquisition. -/
theorem indexLookup_loan (kinds : List IndexKind) (index : Nat) (initial : WGWorld) :
    ⦃fun w => ⌜wgStoreView w = wgStoreView initial⌝⦄ indexLookup kinds index
    ⦃⇓? result w => ⌜Loan initial (result.map Prod.snd) w⌝⦄ := by
  let walk (e : IndexEntry) (s : Option IndexEntry × Bool) : WG.M (ForInStep (Option IndexEntry × Bool)) := do
    _ ← branch .idxWalk true
    if ← branch .idxMatch (e.index == index) then
      if ← branch .idxTypeMatch (kinds.contains e.kind) then
        return .done (some e,true)
      return .done (s.1,true)
    return .yield s
  let scan : WG.M (Option IndexEntry × Bool) := do
    let entries ← liftIndex (indexBucket index)
    forIn entries (none,false) walk
  let tail (s : Option IndexEntry × Bool) : WG.M (Option (IndexOwner × PeerId)) := do
    let (entry,stopped) := s
    if !stopped then _ ← branch .idxWalk false
    if ← branch .idxFound entry.isSome then
      let some e := entry | invariant "unreachable"
      let peer ← Affiliation.acquireOwner e.owner
      if ← branch .idxPeerAlive peer.isSome then
        let some pid := peer | invariant "unreachable"
        return some (e.owner,pid)
    return none
  have factor : indexLookup kinds index = (scan >>= tail) := by
    rw [← Affiliation.indexLookupSource_eq]
    simp only [Affiliation.indexLookupSource,scan,walk,tail,bind_assoc]
    rfl
  have hi : Hoare (liftIndex (indexBucket index))
      (fun w => wgStoreView w = wgStoreView initial)
      (fun _ w => wgStoreView w = wgStoreView initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hw hr
    cases hd : w.dev with
    | none => simp [liftIndex_run,hd] at hr
    | some d =>
      simp [liftIndex_run,indexBucket,hd] at hr
      obtain ⟨rfl,rfl,rfl⟩ := hr
      simpa only [← hd] using hw
  have hwk : ∀ e state, Hoare (walk e state)
      (fun w => wgStoreView w = wgStoreView initial)
      (fun _ w => wgStoreView w = wgStoreView initial) := by
    intro e state
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hw hr
    cases hm : (e.index == index) <;> cases ht : (kinds.contains e.kind) <;>
      simp [walk,branch,hm,ht,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
        CounterWindow.except_ok_bind,CounterWindow.except_pure] at hr
    all_goals rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩; exact hw
  have hs : Hoare scan (fun w => wgStoreView w = wgStoreView initial)
      (fun _ w => wgStoreView w = wgStoreView initial) := by
    apply hoare_bind (Q := fun _ w => wgStoreView w = wgStoreView initial)
    · exact hi
    · intro entries
      exact list_view_spec wgStoreView (fun v => v = wgStoreView initial)
        entries (none,false) walk hwk
  rw [factor]
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hw hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨⟨entry,stopped⟩,a,midway,hscan,htail⟩ := hr
  have stable := (hoare_iff_run_ambient _ _ _).mp hs w ambient _ a midway hw hscan
  have hd := congrArg WGStoreView.dev stable
  change a.dev = initial.dev at hd
  cases stopped <;> cases entry <;>
    simp [tail,branch,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
      CounterWindow.except_ok_bind,CounterWindow.except_pure] at htail
  all_goals try (rcases htail with ⟨⟨rfl,rfl⟩,rfl⟩; exact ⟨by simp [peerView,hd],by simp [rxView,hd]⟩)
  case false.some entry =>
    cases hg : ((Affiliation.acquireOwner entry.owner).run a).run
        (CounterWindow.record (CounterWindow.record midway .idxWalk false) .idxFound true) with
    | error err => simp [hg] at htail
    | ok pair =>
      rcases pair with ⟨⟨peer,b⟩,borrowAmbient⟩
      have loan := (hoare_iff_run_ambient _ _ _).mp (acquireOwner_loan_spec entry.owner initial)
        a _ peer b borrowAmbient stable hg
      cases peer <;> simp [hg,CounterWindow.except_ok_bind,StateT.run_pure,
        CounterWindow.except_pure] at htail
      all_goals rcases htail with ⟨⟨rfl,rfl⟩,rfl⟩; exact loan
  case true.some entry =>
    cases hg : ((Affiliation.acquireOwner entry.owner).run a).run
        (CounterWindow.record midway .idxFound true) with
    | error err => simp [hg] at htail
    | ok pair =>
      rcases pair with ⟨⟨peer,b⟩,borrowAmbient⟩
      have loan := (hoare_iff_run_ambient _ _ _).mp (acquireOwner_loan_spec entry.owner initial)
        a _ peer b borrowAmbient stable hg
      cases peer <;> simp [hg,CounterWindow.except_ok_bind,StateT.run_pure,
        CounterWindow.except_pure] at htail
      all_goals rcases htail with ⟨⟨rfl,rfl⟩,rfl⟩; exact loan

/-- Source store-back, not a global affiliation premise: a returned key owner
has the borrowed peer word in the actual acquisition endpoint. -/
theorem acquireOwner_key_word (id pid : Nat) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((Affiliation.acquireOwner (.keypair id)).run w).run ambient = .ok ((some pid,v),ambient')) :
    ∃ d k, v.dev = some d ∧ d.keypairs[id]? = some k ∧ k.peer = some pid := by
  obtain ⟨word,a,b,readAmbient,borrowedAmbient,hread,hget,hstore⟩ :=
    Affiliation.acquireOwner_acquisition _ _ _ _ _ _ hr
  obtain ⟨d,k,hd,hk,hv,_⟩ := Origins.keypair_word_store id (some pid) b v _ _ hstore
  subst v
  refine ⟨{d with keypairs := d.keypairs.insert id {k with peer := some pid}},
    {k with peer := some pid},?_,?_,rfl⟩
  · simp [CounterWindow.store,hd]
  · simp

theorem credit_balance (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (o : Owner) : balance (creditWorld w d pid p) o =
      if o = ⟨d.ifindex,pid,p.internalId⟩ then balance w o + 1 else balance w o := by
  rcases o with ⟨epoch,slot,stamp⟩
  simp only [balance_factor,peerView,viewBalance,creditWorld,hd,Option.map_some,Option.bind_some]
  by_cases he : d.ifindex = epoch <;> by_cases hi : pid = slot <;>
    by_cases hs : p.internalId = stamp
  all_goals simp_all [Std.TreeMap.getElem?_insert,Owner.mk.injEq]
  all_goals grind

/-- An actual lookup loan extends the given reservation ledger; the extra
reference is never reconstructed from arbitrary endpoint slack. -/
theorem loan_protected (hl : Loan w (some pid) v) (hi : Protected cs loans w) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Protected cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  obtain ⟨d,p,hd,hp,pos,hv,_⟩ := hl
  refine ⟨d,p,hd,hp,pos,?_⟩
  intro o
  have he := (balance_view (o := o) hv).trans (credit_balance hd hp o)
  have old := hi o
  by_cases ho : o = ⟨d.ifindex,pid,p.internalId⟩
  · simp [demand,ho] at *
    omega
  · simp [demand,ho,Ne.symm ho] at *
    omega

theorem loan_to_carrier (hi : Protected cs (c.owner :: loans) w)
    (hc : c.phase.charged = true) : Protected (c :: cs) loans w := by
  intro o
  have old := hi o
  by_cases he : c.owner = o <;> simp [demand,hc,he] at * <;> omega

/-- A genuinely vacant allocation slot extends this same complete inventory.
The caller may obtain vacancy from the existing packet allocation invariant. -/
theorem allocate_inventory (ambient : Ambient) (hi : Inventory cs w) (hd : w.dev = some d)
    (fresh : d.rxSkbs[d.nextSkb]? = none) (owner : o.epoch = d.ifindex)
    (pid : pkt.peer = o.slot) :
    let c : Carrier := ⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩
    let v := Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1}
    ((newRxSkb pkt).run w).run ambient = .ok ((d.nextSkb,v),ambient) ∧ Inventory (c :: cs) v ∧
      peerView v = peerView w := by
  dsimp only
  let c : Carrier := ⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩
  let v := Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1}
  have different : ∀ x ∈ cs, x.packet ≠ c.packet := by
    intro x hx he
    obtain ⟨_,q,hq,_⟩ := hi.present x hx
    rw [he] at hq
    simp [c,packetAt,hd,fresh] at hq
  have keeps : ∀ x ∈ cs, packetAt v x.packet = packetAt w x.packet := by
    intro x hx
    obtain ⟨_,q,hq,_⟩ := hi.present x hx
    have epoch : d.ifindex = x.packet.epoch := by
      by_cases he : d.ifindex = x.packet.epoch
      · exact he
      · simp [packetAt,hd,he] at hq
    have ne : d.nextSkb ≠ x.packet.slot := by
      intro he
      apply different x hx
      cases hx : x.packet
      simp_all [c]
    simp [v,packetAt,Packets.update,hd,epoch,Std.TreeMap.getElem?_insert,ne]
  refine ⟨by simpa [Packets.update,hd] using Packets.newRxSkb_run w ambient d pkt hd,?_,by simp [peerView,Packets.update,hd]⟩
  refine ⟨?_,?_,?_⟩
  · simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,hi.distinct⟩
    intro hm
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    exact different x hx he
  · intro x hx
    rcases List.mem_cons.mp hx with he | hx
    · subst x
      exact ⟨owner.symm,pkt,by simp [packetAt,Packets.update,hd],pid⟩
    · obtain ⟨ep,q,hq,ho⟩ := hi.present x hx
      exact ⟨ep,q,(keeps x hx).trans hq,ho⟩
  · intro out id q hout hq
    have oe : out = {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1} := by simpa [Packets.update,hd] using hout.symm
    subst out
    by_cases he : d.nextSkb = id
    · exact ⟨c,by simp [c],by simp [c,he]⟩
    · have old : d.rxSkbs[id]? = some q := by simpa [Std.TreeMap.getElem?_insert,he] using hq
      obtain ⟨x,hx,h⟩ := hi.complete d id q hd old
      exact ⟨x,by simp [hx],h⟩

/-- Allocation transfers the already-attributed lookup reservation into one
unpublished carrier, retaining the given inventory and every other charge. -/
theorem allocate_transfer (ambient : Ambient) (hi : Inventory cs w) (hd : w.dev = some d)
    (fresh : d.rxSkbs[d.nextSkb]? = none) (owner : o.epoch = d.ifindex)
    (pid : pkt.peer = o.slot) (hs : Protected cs (o :: loans) w) :
    ∃ v, ((newRxSkb pkt).run w).run ambient = .ok ((d.nextSkb,v),ambient) ∧
      Inventory (⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩ :: cs) v ∧
      Protected (⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩ :: cs) loans v := by
  obtain ⟨hr,iv,hv⟩ := allocate_inventory ambient hi hd fresh owner pid
  exact ⟨_,hr,iv,protected_view (loan_to_carrier hs rfl) hv⟩

/-- Current key word at a concrete successful acquisition boundary. -/
def KeyWord (kid pid : Nat) (w : WGWorld) : Prop :=
  ∃ d k, w.dev = some d ∧ d.keypairs[kid]? = some k ∧ k.peer = some pid

theorem acquire_key_spec (owner : IndexOwner) :
    ⦃fun _ => ⌜True⌝⦄ Affiliation.acquireOwner owner
    ⦃⇓? result w => ⌜∀ kid pid, owner = .keypair kid → result = some pid → KeyWord kid pid w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' _ hr kid pid he hp
  subst owner; subst result
  exact acquireOwner_key_word kid pid w v ambient ambient' hr

/-- The full original lookup stores the borrowed peer into the actual returned
key owner. It does not assume an initialized global affiliation invariant. -/
theorem indexLookup_key_word (kinds : List IndexKind) (index : Nat) :
    ⦃fun _ => ⌜True⌝⦄ indexLookup kinds index
    ⦃⇓? result w => ⌜∀ kid pid, result = some (.keypair kid,pid) → KeyWord kid pid w⌝⦄ := by
  let walk (e : IndexEntry) (s : Option IndexEntry × Bool) : WG.M (ForInStep (Option IndexEntry × Bool)) := do
    _ ← branch .idxWalk true
    if ← branch .idxMatch (e.index == index) then
      if ← branch .idxTypeMatch (kinds.contains e.kind) then
        return .done (some e,true)
      return .done (s.1,true)
    return .yield s
  let scan : WG.M (Option IndexEntry × Bool) := do
    let entries ← liftIndex (indexBucket index)
    forIn entries (none,false) walk
  let tail (s : Option IndexEntry × Bool) : WG.M (Option (IndexOwner × PeerId)) := do
    let (entry,stopped) := s
    if !stopped then _ ← branch .idxWalk false
    if ← branch .idxFound entry.isSome then
      let some e := entry | invariant "unreachable"
      let peer ← Affiliation.acquireOwner e.owner
      if ← branch .idxPeerAlive peer.isSome then
        let some pid := peer | invariant "unreachable"
        return some (e.owner,pid)
    return none
  have factor : indexLookup kinds index = (scan >>= tail) := by
    rw [← Affiliation.indexLookupSource_eq]
    simp only [Affiliation.indexLookupSource,scan,walk,tail,bind_assoc]
    rfl
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' _ hr kid pid he
  subst result
  rw [factor,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨⟨entry,stopped⟩,a,midway,hscan,htail⟩ := hr
  cases stopped <;> cases entry <;>
    simp [tail,branch,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
      CounterWindow.except_ok_bind,CounterWindow.except_pure] at htail
  case false.some entry =>
    cases hg : ((Affiliation.acquireOwner entry.owner).run a).run
        (CounterWindow.record (CounterWindow.record midway .idxWalk false) .idxFound true) with
    | error err => simp [hg] at htail
    | ok pair =>
      rcases pair with ⟨⟨peer,b⟩,borrowAmbient⟩
      have word := (hoare_iff_run_ambient _ _ _).mp (acquire_key_spec entry.owner)
        a _ peer b borrowAmbient True.intro hg
      cases peer <;> simp [hg,CounterWindow.except_ok_bind,StateT.run_pure,
        CounterWindow.except_pure] at htail
      rcases htail with ⟨⟨⟨he,rfl⟩,rfl⟩,rfl⟩
      exact word kid _ he rfl
  case true.some entry =>
    cases hg : ((Affiliation.acquireOwner entry.owner).run a).run
        (CounterWindow.record midway .idxFound true) with
    | error err => simp [hg] at htail
    | ok pair =>
      rcases pair with ⟨⟨peer,b⟩,borrowAmbient⟩
      have word := (hoare_iff_run_ambient _ _ _).mp (acquire_key_spec entry.owner)
        a _ peer b borrowAmbient True.intro hg
      cases peer <;> simp [hg,CounterWindow.except_ok_bind,StateT.run_pure,
        CounterWindow.except_pure] at htail
      rcases htail with ⟨⟨⟨he,rfl⟩,rfl⟩,rfl⟩
      exact word kid _ he rfl

theorem keypairGet_credit_frame (kid : Option KeypairId) :
    SameView (fun w => (peerView w,rxView w)) (keypairGet kid) := by
  intro initial
  let P : WGWorld → Prop := fun w => (peerView w,rxView w) = initial
  have getter (id : KeypairId) : Preserves P (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient key v ambient' hi hr
    obtain ⟨rfl, _, _, _, _⟩ := KeyTimes.getKeypair_return id w v key ambient ambient' hr
    exact hi
  have setter (id : KeypairId) (key : Keypair) : Preserves P (setKeypair id key) := by
    unfold setKeypair modifyDev
    apply hoare_modify
    intro w hi
    cases hd : w.dev <;> simpa [P,peerView,rxView,hd] using hi
  change Preserves P (keypairGet kid)
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported,invariant]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter _)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem receiveKey_credit_frame (entry : Option (IndexOwner × PeerId)) :
    SameView (fun w => (peerView w,rxView w)) (Affiliation.receiveKeyAcquire entry) := by
  cases entry with
  | none =>
    intro initial
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hi hr
    simp [Affiliation.receiveKeyAcquire,keypairGetNull,branch,StateT.run_monadLift] at hr
    rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
    exact hi
  | some e =>
    rcases e with ⟨owner,pid⟩
    cases owner with
    | handshake id =>
      intro initial
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient result v ambient' hi hr
      simp [Affiliation.receiveKeyAcquire,invariant,AmbientM.invariant,StateT.run_bind,
        StateT.run_monadLift] at hr
      cases hr
    | keypair id =>
      simpa [Affiliation.receiveKeyAcquire] using
        (keypairGet_credit_frame (some id)).bind (fun _ => SameView.pure _ _)

theorem loan_after_frame (hl : Loan w pid a)
    (hv : peerView b = peerView a) (hx : rxView b = rxView a) : Loan w pid b := by
  cases pid with
  | none => exact ⟨hv.trans hl.1,hx.trans hl.2⟩
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,he,hr⟩ := hl
    exact ⟨d,p,hd,hp,pos,hv.trans he,hx.trans hr⟩

/-- Every actual normal admission reaches allocation with exactly the lookup's
peer loan and the actual packet. The intermediate WGWorlds are consecutive source
cuts, retained independently of whether enqueue or later cleanup succeeds. -/
theorem admitted_loan (ambient ambient' : Ambient)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient = .ok ((some ctx,v),ambient')) :
    ∃ before allocationAmbient, Loan w (some ctx.packet.peer) before ∧
      ((newRxSkb ctx.packet).run before).run allocationAmbient = .ok ((ctx.slot,v),ambient') := by
  obtain ⟨entry,a,aAmbient,b,bAmbient,c,cAmbient,peer,d,dAmbient,e,eAmbient,hl,hk,hno,hp,hd,_,hn⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v ambient ambient' hr
  have entryEq := ((hoare_iff_run_ambient _ _ _).mp
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view a))
    a aAmbient _ b bAmbient rfl hk).2 ctx.packet.keypair ctx.packet.peer rfl
  have loan := (hoare_iff_run_ambient _ _ _).mp (indexLookup_loan [.keypair] (u32le msg 4) w)
    w ambient entry a aAmbient rfl hl
  have fr := Prod.mk.inj ((ProjectedAction.iff_run_ambient _ _ _).mp
    (receiveKey_credit_frame entry) a aAmbient _ b bAmbient hk)
  have lc : Loan w (some ctx.packet.peer) b := loan_after_frame (by simpa [entryEq] using loan) fr.1 fr.2
  have kc : c = b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair false) (fun g => g = b))
    b bAmbient false c cAmbient rfl hno
  have he : d = c := (getPeer_normal ctx.packet.peer c d peer cAmbient dAmbient hp).1
  have ke : e = d := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) (fun g => g = d))
    d dAmbient false e eAmbient rfl hd
  refine ⟨e,eAmbient,loan_after_frame lc ?_ ?_,hn⟩
  all_goals simp only [ke,he,kc]

def publicationMiddle (pid : PeerId) (id : SkbId) (state : PacketState) : WG.M Unit := do
  let p ← getPeer pid
  if !(p.rxQueue.all.contains id) then invariant "a decrypted packet that is not on its peer's rx_queue"
  setRxSkb id fun q => {q with state}
  setPeer pid {p with napiScheduled := true}

theorem publicationMiddle_frame (pid : PeerId) (id : SkbId) (state : PacketState) :
    SameView peerView (publicationMiddle pid id state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hr
  unfold publicationMiddle at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,readAmbient,hg,hr⟩ := hr
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w a p ambient readAmbient hg
  cases contains : p.rxQueue.all.contains id with
  | false =>
    simp only [contains,Bool.not_false,ite_true] at hr
    cases hr
  | true =>
    simp only [contains,Bool.not_true,Bool.false_eq_true,ite_false] at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨x,b,midway,hs,ht⟩ := hr
    let P : WGWorld → Prop := fun g => g.dev.map (fun d => (d.ifindex,d.peers)) = some (d.ifindex,d.peers)
    have frame : Hoare (setRxSkb id (fun q => {q with state})) P (fun _ => P) := by
      unfold setRxSkb
      apply hoare_liftSkb
      intro g dev packets hi hg
      simpa [P,hg] using hi
    have hb := (hoare_iff_run_ambient _ _ _).mp frame a readAmbient x b midway (by simp [P,hd]) hs
    cases hdev : b.dev with
    | none => simp [P,hdev] at hb
    | some db =>
      have fields : db.ifindex = d.ifindex ∧ db.peers = d.peers := by simpa [P,hdev] using hb
      cases ht
      simp only [peerView,hd,hdev,fields.1,fields.2,Option.map_some,Option.bind_some]
      apply Prod.ext
      · rfl
      · funext q
        by_cases he : pid = q
        · subst q
          simp [hp]
        · simp [Std.TreeMap.getElem?_insert,he]

theorem publication_factor (id : SkbId) (state : PacketState) :
    enqueuePerPeerRx (pure ()) id state = (do
      let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)
      peerGet pid
      publicationMiddle pid id state
      peerPut (some pid)) := by
  simp only [enqueuePerPeerRx,publicationMiddle,bind_assoc,pure_bind,liftM,monadLift_self]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | (intro x; try dsimp only)
    | split
    | (simp only [bind_assoc]; done)

/-- Repay the same acquired credit after operations preserving the concrete
peer count/identity view. The preserved projection is a local source contract. -/
theorem credit_repayment (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (pos : 0 < p.refcount)
    (view : peerView b = peerView (creditWorld w d pid p))
    (ambient ambient' : Ambient)
    (hr : ((peerPut (some pid)).run b).run ambient = .ok (((),v),ambient')) :
    ∀ o, balance v o = balance w o := by
  have ep := (Prod.mk.inj view).1
  have slot := congrFun (Prod.mk.inj view).2 pid
  cases hb : b.dev with
  | none => simp [hb,creditWorld] at ep
  | some db =>
    have epoch : db.ifindex = d.ifindex := by simpa [peerView,hb,creditWorld] using ep
    cases hg : db.peers[pid]? with
    | none => simp [hb,hg,creditWorld] at slot
    | some q =>
      have fields : q.internalId = p.internalId ∧ q.refcount = p.refcount + 1 ∧ q.rxQueue = p.rxQueue := by
        simpa [peerView,hb,hg,creditWorld] using slot
      have positive : 0 < q.refcount := by omega
      have effect := (peerPut_effect pid b v db q ambient ambient' hb hg hr).2.1
      intro o
      have hv := (balance_view (o := o) effect).trans (payment_balance hb hg positive o)
      have bv := (balance_view (o := o) view).trans (credit_balance hd hp o)
      rw [epoch,fields.1] at hv
      by_cases he : o = ⟨d.ifindex,pid,p.internalId⟩
      · subst o
        simp only [ite_true] at hv bv
        omega
      · simp only [ite_eq_right he] at hv bv
        omega

/-- The pure-IRQ publication path pays its own freshly acquired reference,
for the actual resolved peer; it need not equal an assumed packet owner. -/
theorem publication_balances (id : SkbId) (state : PacketState) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((enqueuePerPeerRx (pure () : WG.M Unit) id state).run w).run ambient = .ok (((),v),ambient')) :
    ∀ o, balance v o = balance w o := by
  rw [publication_factor] at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,a,aAmbient,hpkt,pid,b,bAmbient,hderef,u,c,cAmbient,hget,u',e,eAmbient,hmid,hput⟩ := hr
  have ka := (Packets.getRxSkb_current id w a pkt ambient aAmbient hpkt).1
  subst a
  have kb : b = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerDeref_preserves (.keypair pkt.keypair) (fun g => g = w))
    w aAmbient pid b bAmbient rfl hderef
  obtain ⟨d,p,hd,hp,pos,hc⟩ := peerGet_loan pid b c bAmbient cAmbient hget
  have hm := (ProjectedAction.iff_run_ambient _ _ _).mp
    (publicationMiddle_frame pid id state) c cAmbient u' e eAmbient hmid
  have hcdev := congrArg WGStoreView.dev hc
  change c.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at hcdev
  have hv : peerView e = peerView (creditWorld w d pid p) := by
    exact hm.trans (by simp only [peerView,creditWorld,hcdev])
  exact credit_repayment (kb ▸ hd) hp pos hv eAmbient ambient' hput

theorem keyWord_affiliation_view (hw : KeyWord kid pid w)
    (he : Affiliation.view v = Affiliation.view w) : KeyWord kid pid v := by
  obtain ⟨d,k,hd,hk,hp⟩ := hw
  have hs := congrArg (fun o => o.bind fun s => s.keys kid) he
  cases hv : v.dev with
  | none => simp [Affiliation.view,Affiliation.state,hd,hv,hk] at hs
  | some dv =>
    cases hvk : dv.keypairs[kid]? with
    | none => simp [Affiliation.view,Affiliation.state,hd,hv,hk,hvk] at hs
    | some kv =>
      have words : kv.peer = k.peer := by
        have h : Affiliation.keyCell kv = Affiliation.keyCell k := by
          simpa [Affiliation.view,Affiliation.state,hd,hv,hk,hvk] using hs
        exact congrArg Prod.snd h
      exact ⟨dv,kv,hv,hvk,words.trans hp⟩

/-- The actual admitted key keeps the successful lookup's locally stored owner
through key acquisition and RX allocation; no global affiliation premise. -/
theorem admitted_key_word (ambient ambient' : Ambient)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient = .ok ((some ctx,v),ambient')) :
    KeyWord ctx.packet.keypair ctx.packet.peer v := by
  obtain ⟨entry,a,aAmbient,b,bAmbient,c,cAmbient,peer,d,dAmbient,e,eAmbient,hl,hk,hno,hp,hd,_,hn⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v ambient ambient' hr
  have ka := (hoare_iff_run_ambient _ _ _).mp
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view a)) a aAmbient _ b bAmbient rfl hk
  have ent := ka.2 ctx.packet.keypair ctx.packet.peer rfl
  have wa := (hoare_iff_run_ambient _ _ _).mp (indexLookup_key_word [.keypair] (u32le msg 4))
    w ambient entry a aAmbient True.intro hl _ _ ent
  have wb := keyWord_affiliation_view wa ka.1
  have kc : c = b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair false) (fun g => g = b))
    b bAmbient false c cAmbient rfl hno
  have he : d = c := (getPeer_normal ctx.packet.peer c d peer cAmbient dAmbient hp).1
  have ke : e = d := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) (fun g => g = d))
    d dAmbient false e eAmbient rfl hd
  have we : KeyWord ctx.packet.keypair ctx.packet.peer e := by
    simpa only [KeyWord,ke,he,kc] using wb
  obtain ⟨dev,key,hdev,hkey,hword⟩ := we
  rw [Packets.newRxSkb_run e eAmbient dev ctx.packet hdev] at hn
  have hv := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hn)).1).2
  rw [← hv]
  exact ⟨{dev with rxSkbs := dev.rxSkbs.insert dev.nextSkb ctx.packet, nextSkb := dev.nextSkb + 1},
    key,by simp [Packets.update,hdev],hkey,hword⟩


/-- The original post-allocation tail, already factored by the receipt layer. -/
def finishSource (ctx : RxOrigin.Admission) : WG.M Unit :=
  RxOrigin.finishWith keypairPut WG.peerPut enqueuePerDeviceAndPeerRx
    (fun id => enqueuePerPeerRx (pure ()) id .dead) freeRxSkb (fun a => a) ctx

def enospcDecisions (ambient : Ambient) : Ambient :=
  CounterWindow.record (CounterWindow.record (CounterWindow.record ambient .dataEpipe false)
    .dataEnqueueOk false) .dataEnqueueOkEpipe false

/-- The negative errno still executes all three recorded decisions, then the
actual key-put/peer-put/free suffix. No successful cleanup endpoint is assumed. -/
theorem finish_enospc (ctx : RxOrigin.Admission) (ambient afterEnqueue : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx ctx.slot).run w).run ambient =
      .ok ((-ENOSPC,a),afterEnqueue)) :
    ((finishSource ctx).run w).run ambient =
      ((discard ctx.slot ctx.packet).run a).run (enospcDecisions afterEnqueue) := by
  simp [finishSource,RxOrigin.finishWith,StateT.run_bind,hr,WG.orM,branch,
    ENOSPC,EPIPE,discard,enospcDecisions,CounterWindow.record,StateT.run_monadLift,
    AmbientM.branch,liftM,monadLift_self]

/-- The actual ENOSPC return is the full-peer-queue branch; later device-ring
refusal and normal publication have different return values. -/
private theorem enqueue_enospc_full (id : SkbId) (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx id).run w).run ambient = .ok ((-ENOSPC,v),ambient')) :
    ∃ d pkt p, v.dev = some d ∧ d.rxSkbs[id]? = some pkt ∧
      d.peers[pkt.peer]? = some p ∧ p.rxQueue.all ≠ [] := by
  simp only [enqueuePerDeviceAndPeerRx,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,a,aa,hs,pkt,b,ab,hg,p,c,ac,hpeer,full,e,ae,hb,hr⟩ := hr
  obtain ⟨hbw,hba,d,hd,hpkt⟩ := Packets.getRxSkb_current id a b pkt aa ab hg
  subst b
  subst ab
  obtain ⟨hcw,hca,d',hd',hpslot⟩ := getPeer_normal pkt.peer a c p aa ac hpeer
  subst c
  subst ac
  have de : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst d'
  change Except.ok ((decide (p.rxQueue.count ≥ MAX_QUEUED_PACKETS),a),
    CounterWindow.record aa .enqueuePeerQueueFull (decide (p.rxQueue.count ≥ MAX_QUEUED_PACKETS))) =
      Except.ok ((full,e),ae) at hb
  cases hb
  by_cases hfull : p.rxQueue.count ≥ MAX_QUEUED_PACKETS
  · simp only [hfull,decide_true,ite_true] at hr
    cases hr
    refine ⟨d,pkt,p,hd,hpkt,hpslot,?_⟩
    intro empty
    have : p.rxQueue.items = [] := (List.append_eq_nil_iff.mp empty).2
    simp [PrevQueue.count,this,MAX_QUEUED_PACKETS] at hfull
  · simp only [hfull,decide_false,Bool.false_eq_true,ite_false,
      MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨u1,a1,t1,h1,d2,a2,t2,h2,cpu,a3,t3,h3,u4,a4,t4,h4,ringFull,a5,t5,h5,hr⟩ := hr
    cases ringFull with
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
      obtain ⟨u6,a6,t6,h6,u7,a7,t7,h7,hr⟩ := hr
      simp [ENOSPC] at hr
    | true => simp [ENOSPC,WG.EPIPE] at hr


/-- A full resident queue contributes a charged carrier besides the unpublished
one. Its existing funding therefore makes this peer payment nonfinal. -/
private theorem enospc_credit (hi : Inventory (c :: cs) w)
    (hs : Protected (c :: cs) loans w) (hq : QueueOwners (c :: cs) w)
    (phase : c.phase = .unpublished)
    (hd : w.dev = some d) (hpkt : d.rxSkbs[c.packet.slot]? = some pkt)
    (hp : d.peers[pkt.peer]? = some p) (nonempty : p.rxQueue.all ≠ []) :
    1 < balance w c.owner := by
  obtain ⟨epoch,stored,hstored,howner⟩ := hi.present c (by simp)
  have he : d.ifindex = c.packet.epoch := by
    by_cases h : d.ifindex = c.packet.epoch
    · exact h
    · simp [packetAt,hd,h] at hstored
  have hpkt_eq : pkt = stored := by
    simpa [packetAt,hd,he,hpkt] using hstored
  have hpowner : pkt.peer = c.owner.slot := hpkt_eq ▸ howner
  have demand_pos : 0 < demand (c :: cs) loans c.owner := by
    simp [demand,phase,Phase.charged]
    omega
  obtain ⟨funded,res,hfunded⟩ := protected_resident hs demand_pos
  obtain ⟨df,hdf,hef,hpf,hsf⟩ := resident_fields res
  have df_eq : df = d := Option.some.inj (hdf.symm.trans hd)
  subst df
  have funded_eq : funded = p := Option.some.inj (hpf.symm.trans (hpowner ▸ hp))
  subst funded
  have own : c.owner = ⟨d.ifindex,pkt.peer,p.internalId⟩ := by
    change Owner.mk c.owner.epoch c.owner.slot c.owner.stamp = _
    rw [hef,hpowner,hsf]
  obtain ⟨id,member⟩ := List.exists_mem_of_ne_nil p.rxQueue.all nonempty
  have count_pos := List.count_pos_iff.mpr member
  rw [hq d pkt.peer p id hd hp] at count_pos
  simp only [List.filter_cons,phase] at count_pos
  simp only [show (Phase.unpublished == Phase.queued) = false from rfl,
    Bool.and_false,Bool.false_eq_true,ite_false] at count_pos
  obtain ⟨other,other_mem⟩ := List.length_pos_iff_exists_mem.mp count_pos
  have fields := List.mem_filter.mp other_mem
  have facts : other ∈ cs ∧ other.packet = ⟨d.ifindex,id⟩ ∧
      other.owner = ⟨d.ifindex,pkt.peer,p.internalId⟩ ∧ other.phase = .queued := by
    simpa [Bool.and_eq_true,and_assoc] using fields
  have charged : other ∈ cs.filter (fun x => x.owner == c.owner && x.phase.charged) := by
    simp [List.mem_filter,facts.1,facts.2.2.1,facts.2.2.2,own,Phase.charged]
  have positive : 0 < charges cs c.owner := List.length_pos_iff_exists_mem.mpr ⟨other,charged⟩
  have bounds := hs c.owner
  simp only [demand,charges_cons,phase,Phase.charged,and_self,ite_true] at bounds
  omega

/-- Concrete ENOSPC source repayment/free from the actual enqueue endpoint.
The supplied unpublished ledger is retained, never reconstructed from counts. -/

theorem enospc_discharge (ctx : RxOrigin.Admission)
    (ambient afterEnqueue afterKey : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx ctx.slot).run w).run ambient =
      .ok ((-ENOSPC,a),afterEnqueue))
    (hi : Inventory (c :: cs) a) (hs : Protected (c :: cs) loans a)
    (hq : QueueOwners (c :: cs) a) (phase : c.phase = .unpublished)
    (slot : c.packet.slot = ctx.slot) (owner : ctx.packet.peer = c.owner.slot)
    (hk : ((keypairPut (some ctx.packet.keypair) false).run a).run
      (enospcDecisions afterEnqueue) = .ok (((),b),afterKey)) :
    ∃ v finalAmbient, ((finishSource ctx).run w).run ambient = .ok (((),v),finalAmbient) ∧
      Inventory cs v ∧ Protected cs loans v ∧ QueueOwners cs v ∧ packetAt v c.packet = none := by
  obtain ⟨d,pkt,p,hd,hpkt,hp,nonempty⟩ := enqueue_enospc_full ctx.slot ambient afterEnqueue hr
  have positive : 1 < balance a c.owner :=
    enospc_credit hi hs hq phase hd (by simpa only [slot] using hpkt) hp nonempty
  have views := Prod.mk.inj ((ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame (some ctx.packet.keypair) false)
    a (enospcDecisions afterEnqueue) () b afterKey hk)
  have remaining : 1 < balance b c.owner := by
    rw [balance_view views.1]
    exact positive
  have resident : ∃ p, resident b c.owner = some p ∧ 1 < p.refcount := by
    cases hres : resident b c.owner with
    | none => simp [balance,hres] at remaining
    | some peer => exact ⟨peer,rfl,by simpa [balance,hres] using remaining⟩
  obtain ⟨peer,hres,hcount⟩ := resident
  obtain ⟨dev,hdev,hepoch,hpeer,hstamp⟩ := resident_fields hres
  obtain ⟨afterPeer,peerAmbient,hput⟩ :=
    peerPut_nonfinal_returns c.owner.slot b dev peer afterKey hdev hpeer hcount
  have selectedSafe := selected_protected (protected_view hs views.1)
    (by simp [phase,Phase.charged])
  have selectedInventory := inventory_selected (inventory_view hi views.2)
  obtain ⟨paidSafe,rxSame,_⟩ := selected_payment_normal selectedSafe rfl afterKey peerAmbient hput
  have paidInventory := inventory_paid (inventory_view selectedInventory rxSame)
  obtain ⟨out,hfree,_,_,_⟩ := paid_free peerAmbient paidInventory paidSafe
  have hdiscard : ((discard c.packet.slot ctx.packet).run a).run
      (enospcDecisions afterEnqueue) = .ok (((),out),peerAmbient) := by
    simpa [discard,StateT.run_bind,hk,owner,hput,selected,
      CounterWindow.except_ok_bind,CounterWindow.except_pure] using hfree
  have complete := discard_unpublished_normal hi hs hq phase owner
    (enospcDecisions afterEnqueue) peerAmbient hdiscard
  refine ⟨out,peerAmbient,?_,complete⟩
  rw [finish_enospc ctx ambient afterEnqueue hr]
  simpa only [slot] using hdiscard

end Leanux.Proofs.WG.Queues.RxCredits
