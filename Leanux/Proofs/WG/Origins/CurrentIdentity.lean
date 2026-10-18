import Leanux.Proofs.WG.Origins.ConfiguredSession

/-! Same-receipt configured support with conditional current peer identity.
The invariant permits key/peer absence, invalid keys and cleared owner words.
Its transport relation describes actual key material and surviving peer fields;
it contains no history, session receipt, or desired authorization conclusion. -/
namespace Leanux.Proofs.WG.CurrentIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.MaterialOrigin

def identity (p : Peer) : Nat × Key := (p.internalId, p.remoteStatic)

def Current (ctx : SessionOrigin.Context) (key : Keypair)
    (peers : PeerId → Option Peer) : Prop :=
  ∀ pid p, key.peer = some pid → peers pid = some p → identity p = identity ctx.peer

/-- All evidence, including the current identity clause, uses this same Context. -/
def Supported (history : List SessionOrigin.Receipt) (epoch : Nat) (slot : KeypairId)
    (key : Keypair) (peers : PeerId → Option Peer) : Prop :=
  ∃ (pid : PeerId) (run : WGRunWitness (Option SessionOrigin.Context))
    (ctx : SessionOrigin.Context) (d : Device) (original : Keypair),
    SessionOrigin.Receipt.material pid run ∈ history ∧ run.Valid (SessionOrigin.front pid) ∧
    run.value = some ctx ∧ ctx.slot = slot ∧ ConfiguredSession.Configured pid run.before ctx ∧
    run.after.dev = some d ∧ d.ifindex = epoch ∧ d.keypairs[slot]? = some original ∧
    original.receiving.isValid = true ∧ original.peer = ctx.word ∧
    material key = material original ∧ Origins.WordLe key.peer ctx.word ∧ Current ctx key peers

def Inv (history : List SessionOrigin.Receipt) (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ (id : KeypairId) (key : Keypair), d.keypairs[id]? = some key → key.receiving.isValid = true →
    Supported history d.ifindex id key (fun pid => d.peers[pid]?)

theorem Supported.configured (h : Supported xs epoch slot key peers) :
    ConfiguredSession.Supported xs epoch slot key := by
  obtain ⟨pid, run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, word, _⟩ := h
  exact ⟨pid, run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, word⟩

theorem Inv.configured (h : Inv xs w) : ConfiguredSession.Inv xs w :=
  fun d hd id key hk valid => (h d hd id key hk valid).configured

theorem Supported.mono (h : Supported xs epoch slot key peers)
    (hm : ∀ r ∈ xs, r ∈ ys) : Supported ys epoch slot key peers := by
  obtain ⟨pid, run, ctx, d, original, hin, rest⟩ := h
  exact ⟨pid, run, ctx, d, original, hm _ hin, rest⟩

theorem Inv.mono (h : Inv xs w) (hm : ∀ r ∈ xs, r ∈ ys) : Inv ys w :=
  fun d hd id key hk valid => (h d hd id key hk valid).mono hm

/-- Fixing the actual non-NULL owner retains one configured witness and its
current-peer comparison. There is no separately chosen historical witness. -/
def ByPeer (history : List SessionOrigin.Receipt) (epoch slot : Nat) (key : Keypair)
    (pid : PeerId) (peers : PeerId → Option Peer) : Prop :=
  ∃ (run : WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
    (d : Device) (original : Keypair),
    SessionOrigin.Receipt.material pid run ∈ history ∧ run.Valid (SessionOrigin.front pid) ∧
    run.value = some ctx ∧ ctx.slot = slot ∧ ConfiguredSession.Configured pid run.before ctx ∧
    run.after.dev = some d ∧ d.ifindex = epoch ∧ d.keypairs[slot]? = some original ∧
    original.receiving.isValid = true ∧ original.peer = ctx.word ∧
    material key = material original ∧ ctx.word = some pid ∧
    ∀ p, peers pid = some p → identity p = identity ctx.peer

theorem ByPeer.configured (h : ByPeer xs epoch slot key pid peers) :
    ConfiguredSession.ByPeer xs epoch slot key pid := by
  obtain ⟨run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, word, _⟩ := h
  exact ⟨run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, word⟩

theorem Supported.byPeer (h : Supported xs epoch slot key peers) (word : key.peer = some pid) :
    ByPeer xs epoch slot key pid peers := by
  obtain ⟨q, run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, keep, current⟩ := h
  have actual : ctx.word = some pid := Origins.WordLe.some (word ▸ keep)
  have self : ctx.word = some q := hc.choose_spec.2.2.2.2
  have eq : q = pid := Option.some.inj (self.symm.trans actual)
  subst q
  exact ⟨run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, actual,
    fun p hp => current pid p word hp⟩

theorem Supported.clear_owner (h : Supported xs epoch slot key peers) :
    Supported xs epoch slot {key with peer := none} peers := by
  obtain ⟨pid, run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, _, _⟩ := h
  refine ⟨pid, run, ctx, d, original, hm, hr, hv, hs, hc, hd, he, hk, valid, hw, mat, Or.inl rfl, ?_⟩
  intro owner p impossible
  cases impossible

/-- New valid keys retain their old allocation/material and keep-or-clear word.
Only a currently named resident peer requires an old peer with the same stamp
and static key. An empty/absent or wholly invalid new device is admissible. -/
def Retains (w v : WGWorld) : Prop :=
  ∀ d, v.dev = some d → ∀ (id : KeypairId) (key : Keypair), d.keypairs[id]? = some key → key.receiving.isValid = true →
    ∃ before old, w.dev = some before ∧ before.ifindex = d.ifindex ∧
      before.keypairs[id]? = some old ∧ old.receiving.isValid = true ∧ Origins.KeyLe key old ∧
      ∀ pid p, key.peer = some pid → d.peers[pid]? = some p →
        ∃ previous, before.peers[pid]? = some previous ∧ identity p = identity previous

theorem Retains.refl (w : WGWorld) : Retains w w := by
  intro d hd id key hk valid
  exact ⟨d, key, hd, rfl, hk, valid, Origins.KeyLe.refl _,
    fun _ p _ hp => ⟨p, hp, rfl⟩⟩

theorem Retains.trans (ha : Retains w u) (hb : Retains u v) : Retains w v := by
  intro d hd id key hk valid
  obtain ⟨middle, midKey, hm, em, hmk, vm, km, pm⟩ := hb d hd id key hk valid
  obtain ⟨before, old, hw, ew, hok, vo, ko, po⟩ := ha middle hm id midKey hmk vm
  refine ⟨before, old, hw, ew.trans em, hok, vo, km.trans ko, ?_⟩
  intro pid p word hp
  obtain ⟨midPeer, hmp, ep⟩ := pm pid p word hp
  have mw : midKey.peer = some pid := Origins.WordLe.some (word ▸ km.2)
  obtain ⟨oldPeer, hop, eo⟩ := po pid midPeer mw hmp
  exact ⟨oldPeer, hop, ep.trans eo⟩

theorem Inv.retain (hi : Inv xs w) (hr : Retains w v) : Inv xs v := by
  intro d hd id key hk valid
  obtain ⟨before, old, hw, epoch, ho, vo, kle, hp⟩ := hr d hd id key hk valid
  obtain ⟨pid, run, ctx, originalDev, original, hm, runValid, hv, slot, hc,
    hdev, he, hkey, ov, ow, mat, word, current⟩ := hi before hw id old ho vo
  refine ⟨pid, run, ctx, originalDev, original, hm, runValid, hv, slot, hc,
    hdev, he.trans epoch, hkey, ov, ow, kle.1.trans mat, kle.2.trans word, ?_⟩
  intro owner peer kw stored
  obtain ⟨oldPeer, oldStored, same⟩ := hp owner peer kw stored
  exact same.trans (current owner oldPeer (Origins.WordLe.some (kw ▸ kle.2)) oldStored)

/-- A source-independent projection to the existing receiving-material relation. -/
theorem Retains.material (hr : Retains w v) : Origins.Retains w v := by
  intro epoch keys hv id key hk valid
  obtain ⟨d, hd, fields⟩ := Option.map_eq_some_iff.mp hv
  have he : d.ifindex = epoch := congrArg Prod.fst fields
  have hs := congrFun (congrArg Prod.snd fields) id
  obtain ⟨before, old, hw, ep, ho, vo, kle, _⟩ := hr d hd id key (hs.trans hk) valid
  exact ⟨(fun q => before.keypairs[q]?), old, by simp [Origins.view, hw, ep, he], ho, vo, kle⟩

/-- The old slot frontier is the boundary relevant to existing owner words.
A newly allocated peer at that frontier is outside this obligation. -/
def BelowRetained (before after : Device) : Prop :=
  ∀ pid p, pid < before.nextPeer → after.peers[pid]? = some p →
    ∃ old, before.peers[pid]? = some old ∧ identity p = identity old

theorem BelowRetained.refl (d : Device) : BelowRetained d d :=
  fun _ p _ hp => ⟨p, hp, rfl⟩

/-- Existing material transport plus bounded nullable owners and concrete peer
field retention is enough; no historical-identity premise is hidden here. -/
theorem retains_of_material (hi : Affiliation.Inv w) (hm : Origins.Retains w v)
    (hp : ∀ before after, w.dev = some before → v.dev = some after →
      before.ifindex = after.ifindex → BelowRetained before after) : Retains w v := by
  intro d hd id key hk valid
  obtain ⟨keys, old, hw, ho, vo, kle⟩ := hm d.ifindex (fun q => d.keypairs[q]?)
    (by simp [Origins.view, hd]) id key hk valid
  obtain ⟨before, hb, fields⟩ := Option.map_eq_some_iff.mp hw
  have he : before.ifindex = d.ifindex := congrArg Prod.fst fields
  have hs := congrFun (congrArg Prod.snd fields) id
  have oldKey : before.keypairs[id]? = some old := hs.trans ho
  refine ⟨before, old, hb, he, oldKey, vo, kle, ?_⟩
  intro pid p word resident
  have oldWord : old.peer = some pid := Origins.WordLe.some (word ▸ kle.2)
  have inv := hi (Affiliation.state before) (by simp [Affiliation.view, hb])
  have bounded : pid < before.nextPeer := inv.words id old.internalId pid
    (by simp [Affiliation.state, Affiliation.keyCell, oldKey, oldWord])
  exact hp before d hb hd he pid p bounded resident

/-- Existing exact configured-view frames already retain stamp/static fields.
Combined with actual material retention, they need no affiliation premise. -/
theorem retains_of_configured_view (hm : Origins.Retains w v)
    (hv : ConfiguredIdentity.view v = ConfiguredIdentity.view w) : Retains w v := by
  intro d hd id key hk valid
  obtain ⟨keys, old, hw, ho, vo, kle⟩ := hm d.ifindex (fun q => d.keypairs[q]?)
    (by simp [Origins.view, hd]) id key hk valid
  obtain ⟨before, hb, fields⟩ := Option.map_eq_some_iff.mp hw
  have he : before.ifindex = d.ifindex := congrArg Prod.fst fields
  have hs := congrFun (congrArg Prod.snd fields) id
  have cells : ConfiguredIdentity.state d = ConfiguredIdentity.state before :=
    Option.some.inj (by simpa [ConfiguredIdentity.view, hd, hb] using hv)
  refine ⟨before, old, hb, he, hs.trans ho, vo, kle, ?_⟩
  intro pid peer _ hp
  have same := congrFun (congrArg ConfiguredIdentity.State.peers cells) pid
  cases prior : before.peers[pid]? with
  | none => simp [ConfiguredIdentity.state, hp, prior] at same
  | some previous =>
    have cell : ConfiguredIdentity.cell peer = ConfiguredIdentity.cell previous := by
      simpa [ConfiguredIdentity.state, hp, prior] using same
    exact ⟨previous, rfl, congrArg (fun c => (c.stamp, c.static)) cell⟩

/-- The actual single-slot key-store update: newly valid contents must retain
the previous allocation/material and may keep or clear its nullable owner. -/
theorem retains_insert_key (w : WGWorld) (d : Device) (id : KeypairId) (key : Keypair)
    (hd : w.dev = some d)
    (safe : key.receiving.isValid = true → ∃ old, d.keypairs[id]? = some old ∧
      old.receiving.isValid = true ∧ Origins.KeyLe key old) :
    Retains w {w with dev := some {d with keypairs := d.keypairs.insert id key}} := by
  intro after ha q current hc valid
  cases ha
  by_cases eq : id = q
  · subst q
    have same : current = key := by simpa using hc.symm
    subst current
    obtain ⟨old, ho, vo, kle⟩ := safe valid
    exact ⟨d, old, hd, rfl, ho, vo, kle, fun _ p _ hp => ⟨p, hp, rfl⟩⟩
  · have old : d.keypairs[q]? = some current := by
      simpa [Std.TreeMap.getElem?_insert, eq] using hc
    exact ⟨d, current, hd, rfl, old, valid, Origins.KeyLe.refl _,
      fun _ p _ hp => ⟨p, hp, rfl⟩⟩

theorem retains_clear_key_owner (w : WGWorld) (d : Device) (id : KeypairId) (key : Keypair)
    (hd : w.dev = some d) (hk : d.keypairs[id]? = some key) :
    Retains w {w with dev := some {d with keypairs := d.keypairs.insert id {key with peer := none}}} := by
  apply retains_insert_key w d id _ hd
  intro valid
  exact ⟨key, hk, valid, rfl, Or.inl rfl⟩

/-- Deleting a peer may leave dangling owner words; no new resident appears. -/
theorem below_erase (d : Device) (pid : PeerId) :
    BelowRetained d {d with peers := d.peers.erase pid} := by
  intro q p _ hp
  by_cases he : pid = q
  · subst q; simp at hp
  · exact ⟨p, by simpa [Std.TreeMap.getElem?_erase, he] using hp, rfl⟩

/-- Cached writes must retain both immutable identity fields of the actual old
cell. Equality of the allocation stamp alone is deliberately insufficient. -/
theorem below_put (d : Device) (pid : PeerId) (old p : Peer)
    (ho : d.peers[pid]? = some old) (same : identity p = identity old) :
    BelowRetained d {d with peers := d.peers.insert pid p} := by
  intro q peer _ hp
  by_cases he : pid = q
  · subst q
    have eq : peer = p := by simpa using hp.symm
    subst peer
    exact ⟨old, ho, same⟩
  · exact ⟨peer, by simpa [Std.TreeMap.getElem?_insert, he] using hp, rfl⟩

/-- Actual fresh-slot geometry: no condition on the newly installed peer is
needed to retain old owners below the entry frontier. -/
theorem below_allocate (d : Device) (p : Peer) :
    BelowRetained d {d with nextPeer := d.nextPeer + 1, peers := d.peers.insert d.nextPeer p} := by
  intro pid peer bound hp
  have ne : d.nextPeer ≠ pid := Ne.symm (Nat.ne_of_lt bound)
  exact ⟨peer, by simpa [Std.TreeMap.getElem?_insert, ne] using hp, rfl⟩

/-- Clearing every receiving-valid bit removes every support obligation. -/
theorem Inv.no_valid (history : List SessionOrigin.Receipt) (w : WGWorld)
    (empty : ∀ d, w.dev = some d → ∀ (id : KeypairId) (k : Keypair), d.keypairs[id]? = some k → k.receiving.isValid = false) :
    Inv history w := by
  intro d hd id k hk valid
  have h := empty d hd id k hk
  simp [h] at valid

theorem Inv.absent (history : List SessionOrigin.Receipt) (w : WGWorld) (hd : w.dev = none) :
    Inv history w := by
  intro d h
  simp [hd] at h

/-- An empty replacement device establishes the invariant at any epoch. This
is initialization/reset, not transport of old receiving material to a new epoch. -/
theorem Inv.empty_keys (history : List SessionOrigin.Receipt) (w : WGWorld)
    (empty : ∀ d, w.dev = some d → d.keypairs = ∅) : Inv history w := by
  intro d hd id key hk _
  have he := empty d hd
  simp [he] at hk

/-- Only the original seven WG fields are needed to recognize the actual
empty fixture. Both network and bare flags are unrestricted. -/
theorem initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  have hd := congrArg WGStoreView.dev hw
  change w.dev = (if net && !bare then some {ifindex := 3, ifname := "wg0"} else none) at hd
  apply Inv.empty_keys
  intro d present
  split at hd
  · have eq : d = {ifindex := 3, ifname := "wg0"} := Option.some.inj (present.symm.trans hd)
    subst d
    rfl
  · simp [hd] at present

end Leanux.Proofs.WG.CurrentIdentity
