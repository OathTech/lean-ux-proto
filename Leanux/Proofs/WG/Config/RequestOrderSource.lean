import Leanux.Proofs.WG.Config.RemainingLoopSource
import Leanux.Proofs.WG.Config.RequestOrderEffects
import Leanux.Proofs.WG.Config.RequestOrderFrames
import Leanux.Proofs.WG.Config.ClearedSources

/-! One receipt-bearing device-request factory and its exact erasure, grammar, validity, and entry linkage. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration
open Internal

private theorem bind_if {α β : Type} (c : Prop) [Decidable c]
    (a b : WG.M α) (f : α → WG.M β) :
    (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem key_factor (attrs : DeviceAttrs) (next : WG.M Int) :
    deviceKeyWith (fun {_} a => a) pubkeyLookup peerPut peerRemove
      precomputeStaticStatic expireCurrentPeerKeypairs sendStagedPackets next attrs =
      (keyStage attrs >>= fun _ => next) := by
  unfold keyStage deviceKeyWith
  simp only [bind_assoc, bind_if, pure_bind]
  congr 1
  funext b
  split
  · split
    · simp only [bind_assoc, bind_if, pure_bind]
      congr 1
      funext d
      congr 1
      funext unchanged
      split
      · congr 1
        funext pub
        congr 1
        funext ok
        split
        · split <;> simp only [bind_assoc, bind_if, pure_bind]
        · rfl
      · rfl
    · rfl
  · rfl

/-- The existing device-update continuation after its first generation write.
This exposes one callback boundary; the peer/key factories remain unchanged. -/
def afterGenerationWith {m : Type → Type} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (clear : PeerId → m Unit) (port : Nat → m Int)
    (removeAll : m Unit) (next : m Int) (attrs : DeviceAttrs) (flags : UInt32) : m Int := do
  let zero (ret : Int) : m Int := do
    _ ← lift (branch .setDevZeroKey attrs.privateKey.isSome)
    return ret
  if ← lift (branch .setDevFwmark attrs.fwmark.isSome) then
    lift (modifyDev fun d => {d with fwmark := attrs.fwmark.getD 0})
    for pid in (← lift getDev).peerList do
      _ ← lift (branch .setDevFwmarkPeerIter true)
      clear pid
    _ ← lift (branch .setDevFwmarkPeerIter false)
  if ← lift (branch .setDevPort attrs.listenPort.isSome) then
    let ret ← port (attrs.listenPort.getD 0)
    if ← lift (branch .setDevPortErr (ret != 0)) then return ← zero ret
  if ← lift (branch .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0)) then removeAll
  next

theorem deviceUpdateWith_entry_factor {m : Type → Type} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (clear : PeerId → m Unit) (port : Nat → m Int)
    (removeAll : m Unit) (next : m Int) (attrs : DeviceAttrs) (flags : UInt32) :
    deviceUpdateWith lift clear port removeAll next attrs flags = (do
      lift (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      afterGenerationWith lift clear port removeAll next attrs flags) := rfl

def record (attrs : DeviceAttrs) (kind : Kind) : WGPrefix Receipt Int :=
  receiptWGObserved (liftWGPrefix (action attrs kind)) (receipt kind)

theorem record_erases (attrs : DeviceAttrs) (kind : Kind) :
    ErasesStatePrefix (record attrs kind) (action attrs kind) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem record_spec (attrs : DeviceAttrs) (kind : Kind) (h0 : List Receipt) :
    StatePrefixEnsures (fun h _ _ => h = h0)
      (fun h => h = h0 ∨ ∃ r, h = h0 ++ [r] ∧ r.kind = kind ∧ Valid attrs r)
      (record attrs kind)
      (fun ret h _ _ => ∃ r, h = h0 ++ [r] ∧ r.kind = kind ∧ r.result = ret ∧ Valid attrs r) := by
  intro w ambient h initial
  subst h
  have hc := runWGPrefix_receiptWGObserved
    (liftWGPrefix (action attrs kind)) (receipt kind) w ambient h0
  rw [runWGPrefix_lift] at hc
  simp only [runWGPrefix, runStatePrefix] at hc
  unfold record
  rw [hc]
  cases run : ((action attrs kind).run w).run ambient with
  | error stop => exact ⟨[], by simp, Or.inl rfl, trivial⟩
  | ok out =>
    rcases out with ⟨⟨ret, v⟩, after⟩
    let r := receipt kind ⟨ret, w, v, ambient, after⟩
    have valid : Valid attrs r := ⟨⟨ret, w, v, ambient, after⟩, run, rfl⟩
    exact ⟨[r], rfl, Or.inr ⟨r, rfl, rfl, valid⟩, r, rfl, rfl, rfl, valid⟩

def peers (attrs : DeviceAttrs) : WGPrefix Receipt Int :=
  devicePeersWith (fun {_} a => liftWGPrefix a) (fun p => record attrs (.peer p)) attrs

def keyed (attrs : DeviceAttrs) : WGPrefix Receipt Int := do
  let _ ← record attrs .keyStage
  peers attrs

def update (attrs : DeviceAttrs) (flags : UInt32) : WGPrefix Receipt Int :=
  afterGenerationWith (fun {_} a => liftWGPrefix a)
    (fun pid => do let _ ← record attrs (.clearSource pid); pure ())
    (fun p => record attrs (.port p))
    (do let _ ← record attrs .replacement; pure ())
    (keyed attrs) attrs flags

def accepted (attrs : DeviceAttrs) (flags : UInt32) : WGPrefix Receipt Int := do
  let _ ← record attrs (.updateEntry flags)
  update attrs flags

def observe (attrs : DeviceAttrs) : WGPrefix Receipt Int :=
  setDeviceWith (fun {_} a => liftWGPrefix a) (accepted attrs) attrs

private theorem lift_erases {α : Type} (a : WG.M α) :
    ErasesStatePrefix (liftWGPrefix a : WGPrefix Receipt α) a := fun _ _ _ => rfl

private theorem peer_erases (attrs : DeviceAttrs) (p : PeerAttrs) :
    ErasesStatePrefix (record attrs (.peer p)) (setPeerCmd p) := record_erases attrs _

private theorem port_erases (attrs : DeviceAttrs) (p : Nat) :
    ErasesStatePrefix (record attrs (.port p)) (setPort p) := record_erases attrs _

theorem peers_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (peers attrs) (Configuration.devicePeersSource attrs) := by
  rw [devicePeersSource_factor]
  unfold peers devicePeersWith
  repeat' first
    | with_reducible exact lift_erases _
    | with_reducible exact peer_erases attrs _
    | with_reducible exact port_erases attrs _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply erasesStatePrefix_forIn
    | (maintenance_intro; try dsimp only)
    | split

theorem keyed_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (keyed attrs) (Configuration.deviceKeySource attrs) := by
  rw [deviceKeySource_factor, key_factor]
  exact erasesStatePrefix_bind (record_erases attrs _) (fun _ => peers_erases attrs)

theorem clear_erases (attrs : DeviceAttrs) (pid : PeerId) :
    ErasesStatePrefix (do let _ ← record attrs (.clearSource pid); pure ()) (clearPeerEndpointSrc pid) := by
  have h := erasesStatePrefix_bind (record_erases attrs (.clearSource pid))
    (fun _ => erasesStatePrefix_pure (E := Receipt) (Outer := WGWorld) (Inner := Ambient) ())
  have unit_bind (a : WG.M Unit) : (a >>= fun _ => pure ()) = a := by
    have eq : (fun (_ : Unit) => (pure () : WG.M Unit)) = pure := by
      funext u; cases u; rfl
    rw [eq, bind_pure]
  simpa only [action, bind_assoc, pure_bind, unit_bind] using h

theorem replacement_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (do let _ ← record attrs .replacement; pure ()) peerRemoveAll := by
  have h := erasesStatePrefix_bind (record_erases attrs .replacement)
    (fun _ => erasesStatePrefix_pure (E := Receipt) (Outer := WGWorld) (Inner := Ambient) ())
  have unit_bind (a : WG.M Unit) : (a >>= fun _ => pure ()) = a := by
    have eq : (fun (_ : Unit) => (pure () : WG.M Unit)) = pure := by
      funext u; cases u; rfl
    rw [eq, bind_pure]
  simpa only [action, bind_assoc, pure_bind, unit_bind] using h

theorem update_erases (attrs : DeviceAttrs) (flags : UInt32) :
    ErasesStatePrefix (update attrs flags)
      (afterGenerationWith (fun {_} a => a) clearPeerEndpointSrc setPort peerRemoveAll
        (Configuration.deviceKeySource attrs) attrs flags) := by
  unfold update afterGenerationWith
  repeat' first
    | with_reducible exact lift_erases _
    | with_reducible exact keyed_erases attrs
    | with_reducible exact clear_erases attrs _
    | with_reducible exact replacement_erases attrs
    | with_reducible exact peer_erases attrs _
    | with_reducible exact port_erases attrs _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply erasesStatePrefix_forIn
    | (maintenance_intro; try dsimp only)
    | split

theorem observe_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (observe attrs) (wgSetDevice attrs) := by
  change ErasesStatePrefix (observe attrs) (Configuration.wgSetDeviceSource attrs)
  rw [setDeviceSource_factor]
  have hn : ∀ flags, ErasesStatePrefix (do
      let _ ← record attrs (.updateEntry flags)
      update attrs flags) (Configuration.deviceUpdateSource attrs flags) := by
    intro flags
    have h := erasesStatePrefix_bind (record_erases attrs (.updateEntry flags))
      (fun _ => update_erases attrs flags)
    simpa only [action, bind_assoc, pure_bind, deviceUpdateSource_factor,
      deviceUpdateWith_entry_factor] using h
  unfold observe accepted setDeviceWith
  repeat' first
    | with_reducible exact lift_erases _
    | with_reducible exact hn _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

private theorem forIn_remaining {α β : Type} (xs : List α) (b : β)
    (body : α → β → WGPrefix Receipt (ForInStep β))
    (I : List α → β → List Receipt → WGWorld → Ambient → Prop)
    (S : List Receipt → Prop) (Q : β → List Receipt → WGWorld → Ambient → Prop)
    (safe : ∀ b h w a, Q b h w a → S h)
    (done : ∀ b h w a, I [] b h w a → S h ∧ Q b h w a)
    (step : ∀ x rest b, StatePrefixEnsures (I (x :: rest) b) S (body x b)
      (fun out => match out with | .done b => Q b | .yield b => I rest b)) :
    StatePrefixEnsures (I xs b) S (forIn xs b body) Q := by
  exact Config.RemainingLoop.forIn_remaining xs b body I S Q safe done step

private theorem quiet {α : Type} (a : WG.M α) (P S : List Receipt → Prop)
    (safe : ∀ h, P h → S h) :
    HistorySpec P S (liftWGPrefix a) (fun _ h => P h) :=
  StatePrefixEnsures.lift a (fun h _ _ hp => safe h hp) (fun _ _ _ _ _ _ hp _ => hp)

private theorem pure_history {α : Type} (x : α) (P S : List Receipt → Prop)
    (safe : ∀ h, P h → S h) :
    HistorySpec P S (pure x) (fun _ h => P h) :=
  StatePrefixEnsures.pure x (fun h _ _ hp => safe h hp) (fun _ _ _ hp => hp)

private theorem record_rule (attrs : DeviceAttrs) (kind : Kind)
    (P S : List Receipt → Prop) (Q : Int → List Receipt → Prop)
    (safe : ∀ h, P h → S h)
    (emitted : ∀ h r, P h → r.kind = kind → Valid attrs r →
      S (h ++ [r]) ∧ Q r.result (h ++ [r])) :
    HistorySpec P S (record attrs kind) Q := by
  intro w ambient h hp
  have hc := runWGPrefix_receiptWGObserved
    (liftWGPrefix (action attrs kind)) (receipt kind) w ambient h
  rw [runWGPrefix_lift] at hc
  simp only [runWGPrefix, runStatePrefix] at hc
  unfold record
  rw [hc]
  cases run : ((action attrs kind).run w).run ambient with
  | error stop => exact ⟨[], by simp, safe h hp, trivial⟩
  | ok out =>
    rcases out with ⟨⟨ret, v⟩, after⟩
    let r := receipt kind ⟨ret, w, v, ambient, after⟩
    have valid : Valid attrs r := ⟨⟨ret, w, v, ambient, after⟩, run, rfl⟩
    exact ⟨[r], rfl, emitted h r hp rfl valid⟩

def mark (site : Decision) (value : Bool) : WGPrefix Receipt Unit :=
  liftWGPrefix (do let _ ← branch site value; pure ())

theorem branch_factor (site : Decision) (value : Bool) :
    (liftWGPrefix (branch site value) : WGPrefix Receipt Bool) =
      (do mark site value; pure value) := rfl

private theorem mark_rule (site : Decision) (value : Bool)
    (P S : List Receipt → Prop) (safe : ∀ h, P h → S h) :
    HistorySpec P S (mark site value) (fun _ h => P h) :=
  quiet _ P S safe

def zero (attrs : DeviceAttrs) (ret : Int) : WGPrefix Receipt Int := do
  mark .setDevZeroKey attrs.privateKey.isSome
  pure ret

def peerBody (attrs : DeviceAttrs) (entry : PeerEntry) (_ : Option Int × Unit) :
    WGPrefix Receipt (ForInStep (Option Int × Unit)) := do
  mark .setDevPeersIter true
  match entry with
  | .malformed =>
    mark .setDevParseErr true
    let ret ← zero attrs (-EINVAL)
    pure (.done (some ret, ()))
  | .attrs p =>
    mark .setDevParseErr false
    let ret ← record attrs (.peer p)
    mark .setDevSetPeerErr (ret < 0)
    if ret < 0 then
      let ret ← zero attrs ret
      pure (.done (some ret, ()))
    else pure (.yield (none, ()))

theorem peers_factor (attrs : DeviceAttrs) :
    peers attrs = (do
      mark .setDevHasPeers attrs.peers.isSome
      if attrs.peers.isSome then
        let out ← forIn (attrs.peers.getD []) (none, ()) (peerBody attrs)
        match out.1 with
        | some ret => pure ret
        | none =>
          mark .setDevPeersIter false
          zero attrs 0
      else zero attrs 0) := by
  unfold peers devicePeersWith peerBody zero
  simp only [branch_factor, bind_assoc, pure_bind, decide_eq_true_eq]
  congr 1
  funext u
  split
  · congr 1
    funext out
    rcases out with ⟨ret,u⟩
    cases ret <;> rfl
  · rfl

private theorem mark_then {α : Type} (site : Decision) (value : Bool)
    {P S : List Receipt → Prop} {Q : α → List Receipt → Prop}
    {a : WGPrefix Receipt α} (safe : ∀ h, P h → S h)
    (next : HistorySpec P S a Q) :
    HistorySpec P S (do mark site value; a) Q :=
  StatePrefixEnsures.bind (mark_rule site value P S safe) (fun _ => next)

private theorem zero_rule (attrs : DeviceAttrs) (ret : Int)
    (P S : List Receipt → Prop) (safe : ∀ h, P h → S h) :
    HistorySpec P S (zero attrs ret) (fun x h => x = ret ∧ P h) := by
  apply mark_then _ _ safe
  exact StatePrefixEnsures.pure ret (fun h _ _ hp => safe h hp)
    (fun _ _ _ hp => ⟨rfl,hp⟩)

private theorem record_peer_rule (attrs : DeviceAttrs) (xs rest : List PeerEntry)
    (p : PeerAttrs) (h0 : List Receipt) (out : Option Int × Unit) :
    HistorySpec (PeerAt xs (.attrs p :: rest) h0 out) (PeerSafe xs h0)
      (record attrs (.peer p)) (AfterPeer xs p rest h0) := by
  apply record_rule
  · exact fun _ point => point.safe
  · intro h r point kind valid
    obtain ⟨_,prior,eq,path⟩ := point
    have next : AfterPeer xs p rest h0 r.result (h ++ [r]) :=
      ⟨prior,r,by simp only [eq,List.append_assoc],path,kind,rfl⟩
    exact ⟨next.safe,next⟩

private theorem peerBody_spec (attrs : DeviceAttrs) (xs rest : List PeerEntry)
    (entry : PeerEntry) (h0 : List Receipt) (out : Option Int × Unit) :
    HistorySpec (PeerAt xs (entry :: rest) h0 out) (PeerSafe xs h0)
      (peerBody attrs entry out)
      (fun step => match step with
        | .done out => PeerDone xs h0 out
        | .yield out => PeerAt xs rest h0 out) := by
  unfold peerBody
  apply mark_then _ _ (fun _ point => point.safe)
  cases entry with
  | malformed =>
    apply mark_then _ _ (fun _ point => point.safe)
    apply StatePrefixEnsures.bind
      (zero_rule attrs (-EINVAL) _ _ (fun _ point => point.safe))
    intro ret
    apply StatePrefixEnsures.pure (show ForInStep (Option Int × Unit) from .done (some ret,()))
    · intro h _ _ point
      exact point.2.safe
    · intro h _ _ point
      obtain ⟨result,_,rs,eq,path⟩ := point
      exact ⟨rs,eq,Or.inr (Or.inl ⟨result,rest,path⟩)⟩
  | attrs p =>
    apply mark_then _ _ (fun _ point => point.safe)
    apply StatePrefixEnsures.bind (record_peer_rule attrs xs rest p h0 out)
    intro ret
    apply mark_then _ _ (fun _ point => point.safe)
    split
    · rename_i negative
      apply StatePrefixEnsures.bind
        (zero_rule attrs ret _ _ (fun _ point => point.safe))
      intro same
      apply StatePrefixEnsures.pure (show ForInStep (Option Int × Unit) from .done (some same,()))
      · intro h _ _ point
        exact point.2.safe
      · intro h _ _ point
        obtain ⟨rfl,point⟩ := point
        exact point.negative negative
    · rename_i nonnegative
      apply StatePrefixEnsures.pure (show ForInStep (Option Int × Unit) from .yield (none,()))
      · exact fun _ _ _ point => point.safe
      · exact fun _ _ _ point => point.nonnegative nonnegative

theorem peerLoop_spec (attrs : DeviceAttrs) (xs rest : List PeerEntry)
    (h0 : List Receipt) (out : Option Int × Unit) :
    HistorySpec (PeerAt xs rest h0 out) (PeerSafe xs h0)
      (forIn rest out (peerBody attrs)) (PeerDone xs h0) := by
  apply forIn_remaining rest out (peerBody attrs)
    (fun rest out h _ _ => PeerAt xs rest h0 out h)
  · exact fun _ _ _ _ point => point.safe
  · intro out h _ _ point
    obtain ⟨none,rs,eq,path⟩ := point
    exact ⟨⟨rs,eq,Or.inl ⟨[],path⟩⟩,rs,eq,by simpa only [none] using path⟩
  · intro entry tail out
    exact (peerBody_spec attrs xs tail entry h0 out).consequence (fun _ _ _ point => point)
      (fun step _ _ _ point => by cases step <;> exact point)

theorem peers_spec (attrs : DeviceAttrs) (h0 : List Receipt) :
    HistorySpec (fun h => h = h0) (PeerSafe (attrs.peers.getD []) h0) (peers attrs)
      (fun ret h => ∃ rs, h = h0 ++ rs ∧ PeerFinished (attrs.peers.getD []) rs ret) := by
  rw [peers_factor]
  have initial : ∀ h, h = h0 → PeerSafe (attrs.peers.getD []) h0 h := by
    intro h eq
    exact ⟨[],by simpa using eq,Or.inl ⟨attrs.peers.getD [],.nil _⟩⟩
  apply mark_then _ _ initial
  split
  · have enter : HistorySpec (fun h => h = h0) (PeerSafe (attrs.peers.getD []) h0)
        (forIn (attrs.peers.getD []) (none,()) (peerBody attrs))
        (PeerDone (attrs.peers.getD []) h0) :=
      (peerLoop_spec attrs (attrs.peers.getD []) (attrs.peers.getD []) h0 (none,())).consequence
        (fun h _ _ eq => ⟨rfl,[],by simpa using eq,.nil _⟩)
        (fun _ _ _ _ point => point)
    apply StatePrefixEnsures.bind enter
    intro out
    cases result : out.1 with
    | some ret =>
      apply StatePrefixEnsures.pure ret
      · exact fun _ _ _ point => point.safe
      · intro h _ _ point
        obtain ⟨rs,eq,finish⟩ := point
        exact ⟨rs,eq,by simpa only [result] using finish⟩
    | none =>
      apply mark_then _ _ (fun _ point => point.safe)
      apply (zero_rule attrs 0 (PeerDone (attrs.peers.getD []) h0 out)
        (PeerSafe (attrs.peers.getD []) h0) (fun _ point => point.safe)).consequence
        (fun _ _ _ point => point)
      intro ret h _ _ point
      obtain ⟨rfl,rs,eq,finish⟩ := point
      exact ⟨rs,eq,Or.inl ⟨rfl,by simpa only [result] using finish⟩⟩
  · rename_i missing
    have empty : attrs.peers.getD [] = [] := by
      cases h : attrs.peers with
      | none => rfl
      | some peers => simp only [h,Option.isSome_some] at missing; contradiction
    apply (zero_rule attrs 0 _ _ initial).consequence (fun _ _ _ eq => eq)
    intro ret h _ _ point
    obtain ⟨rfl,rfl⟩ := point
    exact ⟨[],by simp,Or.inl ⟨rfl,by rw [empty]; exact .nil []⟩⟩

theorem conforms_of_history {α : Type} {a : WGPrefix Receipt α} {L : Language α}
    (ha : ∀ h0, HistorySpec (fun h => h = h0) (Segment L.prefixes h0) a
      (fun ret => Segment (L.normal ret) h0)) : Conforms a L := by
  intro w ambient h
  obtain ⟨suffix,eq,safe,post⟩ := ha h w ambient h rfl
  refine ⟨suffix,eq,?_,?_⟩
  · obtain ⟨added,history,point⟩ := safe
    have same : suffix = added := List.append_cancel_left (eq.symm.trans history)
    simpa only [same] using point
  · cases run : runWGPrefix a w ambient h with
    | mk result hist =>
      cases result with
      | error stop => trivial
      | ok out =>
        rcases out with ⟨⟨ret,v⟩,after⟩
        simp only [runWGPrefix,runStatePrefix] at run
        simp only [run] at post eq
        obtain ⟨added,history,point⟩ := post
        have same : suffix = added := List.append_cancel_left (eq.symm.trans history)
        simpa only [Finished,same] using point

theorem record_conforms (attrs : DeviceAttrs) (kind : Kind) :
    Conforms (record attrs kind) (Language.event kind) := by
  apply conforms_of_history
  intro h0
  exact record_rule attrs kind _ _ _
    (fun h eq => ⟨[],by simpa using eq,Or.inl rfl⟩)
    (fun h r eq kind _ => by
      subst h
      exact ⟨⟨[r],rfl,Or.inr ⟨r,rfl,kind⟩⟩,[r],rfl,r,rfl,kind,rfl⟩)

theorem peers_conforms (attrs : DeviceAttrs) :
    Conforms (peers attrs) (Language.peers attrs) := conforms_of_history (peers_spec attrs)

theorem Conforms.weaken {α : Type} {a : WGPrefix Receipt α} {A B : Language α}
    (ha : Conforms a A)
    (prefixes : ∀ h, A.prefixes h → B.prefixes h)
    (normal : ∀ ret h, A.normal ret h → B.normal ret h) : Conforms a B := by
  intro w ambient h
  obtain ⟨added,eq,safe,post⟩ := ha w ambient h
  refine ⟨added,eq,prefixes added safe,?_⟩
  cases run : (runWGPrefix a w ambient h).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    exact normal ret added (by simpa only [Finished,run] using post)

theorem Conforms.bind {α β : Type} {a : WGPrefix Receipt α}
    {b : α → WGPrefix Receipt β} {A : Language α} {B : α → Language β}
    (ha : Conforms a A) (hb : ∀ x, Conforms (b x) (B x)) :
    Conforms (a >>= b) (A.bind B) := by
  intro w ambient h
  obtain ⟨left,he,hs,hq⟩ := ha w ambient h
  change ∃ added, (runStatePrefix (a >>= b) w ambient h).2 = h ++ added ∧
    (A.bind B).prefixes added ∧ Finished (A.bind B) (runStatePrefix (a >>= b) w ambient h).1 added
  rw [runStatePrefix_bind]
  cases first : runStatePrefix a w ambient h with
  | mk result middle =>
    have history : middle = h ++ left := by simpa only [runWGPrefix,first] using he
    cases result with
    | error stop => exact ⟨left,history,Or.inl hs,trivial⟩
    | ok out =>
      rcases out with ⟨⟨x,v⟩,during⟩
      have firstNormal : A.normal x left := by simpa only [runWGPrefix,first,Finished] using hq
      obtain ⟨right,he',hs',hq'⟩ := hb x v during middle
      refine ⟨left ++ right,?_,Or.inr ⟨x,left,right,firstNormal,hs',rfl⟩,?_⟩
      · simpa only [runWGPrefix,history,List.append_assoc] using he'
      · cases last : (runWGPrefix (b x) v during middle).1 with
        | error stop =>
          simp only [runWGPrefix] at last
          simp only [Finished,last]
        | ok out =>
          rcases out with ⟨⟨y,z⟩,after⟩
          have lastNormal : (B x).normal y right := by simpa only [Finished,last] using hq'
          simp only [runWGPrefix] at last
          simpa only [Finished,last,Language.bind] using
            (show ∃ a l r, A.normal a l ∧ (B a).normal y r ∧ left ++ right = l ++ r from
              ⟨x,left,right,firstNormal,lastNormal,rfl⟩)

theorem Conforms.pure {α : Type} (x : α) :
    Conforms (pure x) (Language.returning x) :=
  fun _ _ h => ⟨[],by simp only [runWGPrefix,runStatePrefix_pure,List.append_nil],rfl,rfl,rfl⟩

theorem Conforms.quiet_then {α β : Type} (a : WG.M α)
    {b : α → WGPrefix Receipt β} {L : Language β}
    (empty : L.prefixes []) (next : ∀ x, Conforms (b x) L) :
    Conforms (liftWGPrefix a >>= b) L := by
  intro w ambient h
  change ∃ added, (runStatePrefix (liftWGPrefix a >>= b) w ambient h).2 = h ++ added ∧
    L.prefixes added ∧ Finished L (runStatePrefix (liftWGPrefix a >>= b) w ambient h).1 added
  rw [runStatePrefix_bind]
  have native : runStatePrefix (liftWGPrefix a : WGPrefix Receipt α) w ambient h =
      ((a.run w).run ambient,h) := rfl
  rw [native]
  cases run : (a.run w).run ambient with
  | error stop => exact ⟨[],by simp,empty,trivial⟩
  | ok out =>
    rcases out with ⟨⟨x,v⟩,after⟩
    exact next x v after h

theorem Conforms.mark_then {α : Type} (site : Decision) (value : Bool)
    {a : WGPrefix Receipt α} {L : Language α}
    (empty : L.prefixes []) (next : Conforms a L) :
    Conforms (do mark site value; a) L :=
  Conforms.quiet_then _ empty (fun _ => next)

theorem zero_conforms (attrs : DeviceAttrs) (ret : Int) :
    Conforms (zero attrs ret) (Language.returning ret) :=
  Conforms.mark_then _ _ rfl (Conforms.pure ret)

theorem keyed_conforms (attrs : DeviceAttrs) :
    Conforms (keyed attrs) (keyedLanguage attrs) :=
  (record_conforms attrs .keyStage).bind (fun _ => peers_conforms attrs)

def afterPort (attrs : DeviceAttrs) (flags : UInt32) : WGPrefix Receipt Int := do
  mark .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0)
  if flags &&& WGDEVICE_F_REPLACE_PEERS != 0 then
    let _ ← record attrs .replacement
    keyed attrs
  else keyed attrs

theorem afterPort_conforms (attrs : DeviceAttrs) (flags : UInt32) :
    Conforms (afterPort attrs flags) (afterPortLanguage attrs flags) := by
  apply Conforms.mark_then _ _ (afterPort_empty attrs flags)
  unfold afterPortLanguage
  split
  · exact (record_conforms attrs .replacement).bind (fun _ => keyed_conforms attrs)
  · exact keyed_conforms attrs

def afterFwmark (attrs : DeviceAttrs) (flags : UInt32) : WGPrefix Receipt Int := do
  mark .setDevPort attrs.listenPort.isSome
  if attrs.listenPort.isSome then
    let ret ← record attrs (.port (attrs.listenPort.getD 0))
    mark .setDevPortErr (ret != 0)
    if ret != 0 then zero attrs ret else afterPort attrs flags
  else afterPort attrs flags

theorem afterFwmark_conforms (attrs : DeviceAttrs) (flags : UInt32) :
    Conforms (afterFwmark attrs flags) (afterFwmarkLanguage attrs flags) := by
  apply Conforms.mark_then _ _ (afterFwmark_empty attrs flags)
  unfold afterFwmarkLanguage
  split
  · apply (record_conforms attrs _).bind
    intro ret
    apply Conforms.mark_then _ _
    · split
      · rfl
      · exact afterPort_empty attrs flags
    · split
      · exact zero_conforms attrs ret
      · exact afterPort_conforms attrs flags
  · exact afterPort_conforms attrs flags

theorem Conforms.closed_bind {α β : Type} {P : List Receipt → Prop}
    {a : WGPrefix Receipt α} {b : α → WGPrefix Receipt β}
    (append : ∀ l r, P l → P r → P (l ++ r))
    (ha : Conforms a (Language.closed P))
    (hb : ∀ x, Conforms (b x) (Language.closed P)) :
    Conforms (a >>= b) (Language.closed P) := by
  apply (ha.bind hb).weaken
  · intro h path
    rcases path with left | ⟨_,l,r,hl,hr,rfl⟩
    · exact left
    · exact append l r hl hr
  · intro _ _ path
    obtain ⟨_,l,r,hl,hr,rfl⟩ := path
    exact append l r hl hr

theorem Conforms.closed_pure {α : Type} (x : α) (P : List Receipt → Prop) (empty : P []) :
    Conforms (Pure.pure x) (Language.closed P) :=
  (Conforms.pure x).weaken (fun _ h => h ▸ empty) (fun _ _ h => h.2 ▸ empty)

theorem Conforms.closed_forIn {α β : Type} (xs : List α) (init : β)
    (body : α → β → WGPrefix Receipt (ForInStep β)) (P : List Receipt → Prop)
    (empty : P []) (append : ∀ l r, P l → P r → P (l ++ r))
    (step : ∀ x b, Conforms (body x b) (Language.closed P)) :
    Conforms (forIn xs init body) (Language.closed P) := by
  induction xs generalizing init with
  | nil => exact Conforms.closed_pure init P empty
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply Conforms.closed_bind append (step x init)
    intro out
    cases out with
    | done b => exact Conforms.closed_pure b P empty
    | yield b => exact ih b

theorem clear_conforms (attrs : DeviceAttrs) (pid : PeerId)
    (present : attrs.fwmark.isSome = true) :
    Conforms (record attrs (.clearSource pid)) (Language.closed (ClearPrefix attrs)) := by
  apply (record_conforms attrs _).weaken
  · intro h path
    rcases path with rfl | ⟨r,rfl,kind⟩
    · exact ClearPrefix.empty attrs
    · exact ClearPrefix.singleton present kind
  · intro _ _ path
    obtain ⟨r,rfl,kind,_⟩ := path
    exact ClearPrefix.singleton present kind

theorem update_factor (attrs : DeviceAttrs) (flags : UInt32) :
    update attrs flags = ((do
      mark .setDevFwmark attrs.fwmark.isSome
      if attrs.fwmark.isSome then
        liftWGPrefix (modifyDev fun d => {d with fwmark := attrs.fwmark.getD 0})
        let d ← liftWGPrefix getDev
        for pid in d.peerList do
          mark .setDevFwmarkPeerIter true
          let _ ← record attrs (.clearSource pid)
        mark .setDevFwmarkPeerIter false
      else pure ()) >>= fun _ => afterFwmark attrs flags) := by
  unfold update afterGenerationWith afterFwmark afterPort zero
  simp only [branch_factor,bind_assoc,pure_bind]
  congr 1
  funext u
  split <;> simp only [bind_assoc,pure_bind]

theorem quiet_closed {α : Type} (a : WG.M α) (P : List Receipt → Prop)
    (empty : P []) : Conforms (liftWGPrefix a) (Language.closed P) := by
  intro w ambient h
  refine ⟨[],by simp only [runWGPrefix_lift,List.append_nil],empty,?_⟩
  rw [runWGPrefix_lift]
  cases (a.run w).run ambient with
  | error stop => trivial
  | ok out => exact empty

def fwmarkObserved (attrs : DeviceAttrs) : WGPrefix Receipt Unit := do
  mark .setDevFwmark attrs.fwmark.isSome
  if attrs.fwmark.isSome then
    liftWGPrefix (modifyDev fun d => {d with fwmark := attrs.fwmark.getD 0})
    let d ← liftWGPrefix getDev
    for pid in d.peerList do
      mark .setDevFwmarkPeerIter true
      let _ ← record attrs (.clearSource pid)
    mark .setDevFwmarkPeerIter false
  else pure ()

def fwmarkSource (attrs : DeviceAttrs) : WG.M Unit := do
  (do let _ ← branch .setDevFwmark attrs.fwmark.isSome; pure ())
  if attrs.fwmark.isSome then
    modifyDev fun d => {d with fwmark := attrs.fwmark.getD 0}
    let d ← getDev
    fwmarkClearLoop d.peerList
    _ ← branch .setDevFwmarkPeerIter false

theorem update_fwmark_factor (attrs : DeviceAttrs) (flags : UInt32) :
    update attrs flags = (fwmarkObserved attrs >>= fun _ => afterFwmark attrs flags) :=
  update_factor attrs flags

theorem fwmarkObserved_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (fwmarkObserved attrs) (fwmarkSource attrs) := by
  unfold fwmarkObserved fwmarkSource
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  split
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro d
    apply erasesStatePrefix_bind
    · have grouped : fwmarkClearLoop d.peerList = (forIn d.peerList () fun pid _ => do
        (do let _ ← branch .setDevFwmarkPeerIter true; pure ())
        clearPeerEndpointSrc pid
        pure (ForInStep.yield ())) := by
        simp [fwmarkClearLoop]
      rw [grouped]
      apply erasesStatePrefix_forIn
      intro pid _
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro _
      have h := erasesStatePrefix_bind (clear_erases attrs pid)
        (fun _ => erasesStatePrefix_pure (ForInStep.yield ()))
      simpa only [bind_assoc, pure_bind] using h
    · intro _
      exact erasesStatePrefix_lift _
  · exact erasesStatePrefix_pure ()

theorem fwmarkObserved_conforms (attrs : DeviceAttrs) :
    Conforms (fwmarkObserved attrs) (Language.closed (ClearPrefix attrs)) := by
  unfold fwmarkObserved
  apply Conforms.mark_then _ _ (ClearPrefix.empty attrs)
  split
  · rename_i present
    apply Conforms.quiet_then _ (ClearPrefix.empty attrs)
    intro _
    apply Conforms.quiet_then _ (ClearPrefix.empty attrs)
    intro d
    apply Conforms.closed_bind (fun _ _ => ClearPrefix.append)
    · apply Conforms.closed_forIn _ _ _ _ (ClearPrefix.empty attrs)
        (fun _ _ => ClearPrefix.append)
      intro pid state
      apply Conforms.mark_then _ _ (ClearPrefix.empty attrs)
      apply Conforms.closed_bind (fun _ _ => ClearPrefix.append) (clear_conforms attrs pid present)
      intro _
      exact Conforms.closed_pure _ _ (ClearPrefix.empty attrs)
    · intro _
      exact quiet_closed _ _ (ClearPrefix.empty attrs)
  · exact Conforms.closed_pure () _ (ClearPrefix.empty attrs)

theorem update_conforms (attrs : DeviceAttrs) (flags : UInt32) :
    Conforms (update attrs flags) (updateLanguage attrs flags) := by
  rw [update_fwmark_factor]
  exact Conforms.bind (fwmarkObserved_conforms attrs) (fun _ => afterFwmark_conforms attrs flags)

theorem request_pure (attrs : DeviceAttrs) (ret : Int) :
    Conforms (pure ret) (requestLanguage attrs) :=
  (Conforms.pure ret).weaken (fun _ h => h ▸ request_empty attrs)
    (fun _ _ h => Or.inl h.2)

theorem updateEntry_conforms (attrs : DeviceAttrs) :
    Conforms (do
      let _ ← record attrs (.updateEntry (attrs.flags.getD 0))
      update attrs (attrs.flags.getD 0)) (requestLanguage attrs) :=
  ((record_conforms attrs _).bind (fun _ => update_conforms attrs _)).weaken
    (fun _ point => point) (fun _ _ point => Or.inr point)

theorem observe_conforms (attrs : DeviceAttrs) :
    Conforms (observe attrs) (requestLanguage attrs) := by
  have next := updateEntry_conforms attrs
  unfold observe accepted setDeviceWith
  simp only [branch_factor,bind_assoc,pure_bind]
  cases flags : attrs.flags <;>
    simp only [flags,Option.isSome_none,Option.isSome_some,Option.getD_none,Option.getD_some,
      Bool.false_eq_true,ite_false,ite_true] at next ⊢
  all_goals
    repeat' first
      | with_reducible exact next
      | with_reducible exact request_pure attrs _
      | (maintenance_head mark
         apply Conforms.mark_then _ _ (request_empty attrs))
      | (maintenance_head Bind.bind
         apply Conforms.quiet_then _ (request_empty attrs))
      | (maintenance_intro; try dsimp only)
      | split

theorem record_valid (attrs : DeviceAttrs) (kind : Kind) :
    HistorySpec (ValidHistory attrs) (ValidHistory attrs) (record attrs kind)
      (fun _ => ValidHistory attrs) := by
  apply record_rule
  · exact fun _ point => point
  · intro h r point _ valid
    have all : ValidHistory attrs (h ++ [r]) := by
      intro e member
      rcases List.mem_append.mp member with prior | last
      · exact point e prior
      · have same := List.mem_singleton.mp last
        subst e
        exact valid
    exact ⟨all,all⟩

private theorem valid_forIn (attrs : DeviceAttrs) {α β : Type}
    (xs : List α) (init : β) (body : α → β → WGPrefix Receipt (ForInStep β))
    (step : ∀ x b, HistorySpec (ValidHistory attrs) (ValidHistory attrs)
      (body x b) (fun _ => ValidHistory attrs)) :
    HistorySpec (ValidHistory attrs) (ValidHistory attrs)
      (forIn xs init body) (fun _ => ValidHistory attrs) :=
  StatePrefixEnsures.forInInvariant xs init body (fun _ h _ _ => ValidHistory attrs h)
    (ValidHistory attrs) (fun _ _ _ _ point => point) step

theorem peers_valid (attrs : DeviceAttrs) :
    HistorySpec (ValidHistory attrs) (ValidHistory attrs) (peers attrs)
      (fun _ => ValidHistory attrs) := by
  unfold peers devicePeersWith
  repeat' first
    | with_reducible exact record_valid attrs _
    | with_reducible exact quiet _ _ _ (fun _ point => point)
    | with_reducible exact pure_history _ _ _ (fun _ point => point)
    | with_reducible apply StatePrefixEnsures.bind
    | (maintenance_head ForIn.forIn; apply valid_forIn attrs)
    | (maintenance_intro; try dsimp only)
    | split

theorem keyed_valid (attrs : DeviceAttrs) :
    HistorySpec (ValidHistory attrs) (ValidHistory attrs) (keyed attrs)
      (fun _ => ValidHistory attrs) :=
  StatePrefixEnsures.bind (record_valid attrs .keyStage) (fun _ => peers_valid attrs)

theorem update_valid (attrs : DeviceAttrs) (flags : UInt32) :
    HistorySpec (ValidHistory attrs) (ValidHistory attrs) (update attrs flags)
      (fun _ => ValidHistory attrs) := by
  unfold update afterGenerationWith
  repeat' first
    | with_reducible exact keyed_valid attrs
    | with_reducible exact record_valid attrs _
    | with_reducible exact quiet _ _ _ (fun _ point => point)
    | with_reducible exact pure_history _ _ _ (fun _ point => point)
    | with_reducible apply StatePrefixEnsures.bind
    | (maintenance_head ForIn.forIn; apply valid_forIn attrs)
    | (maintenance_intro; try dsimp only)
    | split

theorem observe_valid (attrs : DeviceAttrs) :
    HistorySpec (ValidHistory attrs) (ValidHistory attrs) (observe attrs)
      (fun _ => ValidHistory attrs) := by
  unfold observe accepted setDeviceWith
  repeat' first
    | with_reducible exact update_valid attrs _
    | with_reducible exact record_valid attrs _
    | with_reducible exact quiet _ _ _ (fun _ point => point)
    | with_reducible exact pure_history _ _ _ (fun _ point => point)
    | with_reducible apply StatePrefixEnsures.bind
    | (maintenance_intro; try dsimp only)
    | split

private theorem entry_record (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient) :
    StatePrefixEnsures (fun h w _ => h = [] ∧ w = initial)
      (PreludeSafe attrs (Campaign2.snapshot initial a).wg)
      (record attrs (.updateEntry (attrs.flags.getD 0)))
      (fun _ h _ _ => Begun attrs (Campaign2.snapshot initial a).wg h) := by
  intro w ambient h point
  rcases point with ⟨rfl,rfl⟩
  let v : WGWorld := {w with dev := w.dev.map fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}}
  let r := receipt (.updateEntry (attrs.flags.getD 0)) ⟨0,w,v,ambient,ambient⟩
  have effect : EntryReceipt attrs (Campaign2.snapshot w a).wg r := ⟨rfl,rfl,rfl,rfl⟩
  exact ⟨[r],rfl,Or.inr ⟨r,[],rfl,effect⟩,r,[],rfl,effect⟩

private theorem after_entry {α : Type} (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient)
    (action : WGPrefix Receipt α) (L : Language α) (law : Conforms action L) :
    StatePrefixEnsures (fun h _ _ => Begun attrs (Campaign2.snapshot initial a).wg h)
      (PreludeSafe attrs (Campaign2.snapshot initial a).wg) action
      (fun _ h w _ => PreludePost attrs initial a h w) := by
  intro w ambient h point
  obtain ⟨added,eq,_,_⟩ := law w ambient h
  have begun : Begun attrs (Campaign2.snapshot initial a).wg
      (runWGPrefix action w ambient h).2 := eq ▸ point.append added
  refine ⟨added,eq,Or.inr begun,?_⟩
  simp only [runWGPrefix,runStatePrefix] at begun ⊢
  cases run : (runPrefix (action.run w) ambient h).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    exact Or.inr begun

open Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes in
private theorem prelude_quiet {α : Type} (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient)
    (action : WG.M α) (frame : SameView (id : WGWorld → WGWorld) action) :
    StatePrefixEnsures (fun h w _ => h = [] ∧ w = initial)
      (PreludeSafe attrs (Campaign2.snapshot initial a).wg) (liftWGPrefix action)
      (fun _ h w _ => h = [] ∧ w = initial) := by
  apply StatePrefixEnsures.lift action
  · exact fun _ _ _ point => Or.inl point.1
  · intro h w ambient ret v after point run
    exact ⟨point.1,(ProjectedAction.iff_run_ambient _ _ _).mp frame
      w ambient ret v after run |>.trans point.2⟩

private theorem prelude_pure (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient) (ret : Int) :
    StatePrefixEnsures (fun h w _ => h = [] ∧ w = initial)
      (PreludeSafe attrs (Campaign2.snapshot initial a).wg) (pure ret : WGPrefix Receipt Int)
      (fun _ h w _ => PreludePost attrs initial a h w) :=
  StatePrefixEnsures.pure ret (fun _ _ _ point => Or.inl point.1)
    (fun _ _ _ point => Or.inl point)

open Leanux.Proofs.Framing in
private theorem prelude_mark (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient)
    (site : Decision) (value : Bool) :
    StatePrefixEnsures (fun h w _ => h = [] ∧ w = initial)
      (PreludeSafe attrs (Campaign2.snapshot initial a).wg) (mark site value)
      (fun _ h w _ => h = [] ∧ w = initial) :=
  prelude_quiet attrs initial a _
    ((ambient_frame (AmbientM.branch site value)).bind (fun _ => SameView.pure _ ()))

theorem observe_entry_rule (attrs : DeviceAttrs)
    {P : List Receipt → WGWorld → Ambient → Prop} {S : List Receipt → Prop}
    {Q : Int → List Receipt → WGWorld → Ambient → Prop}
    (early : ∀ ret, StatePrefixEnsures P S (pure ret) Q)
    (marks : ∀ site value, StatePrefixPreserves P S (mark site value))
    (lookup : StatePrefixPreserves P S (liftWGPrefix (lookupInterface attrs.device)))
    (read : StatePrefixPreserves P S (liftWGPrefix getDev))
    (bad : StatePrefixPreserves P S (liftWGPrefix (invariant "unreachable" : WG.M Int)))
    (or : ∀ left right a b, StatePrefixPreserves P S
      (liftWGPrefix (WG.orM (branch left a) (branch right b))))
    (next : StatePrefixEnsures P S (accepted attrs (attrs.flags.getD 0)) Q) :
    StatePrefixEnsures P S (observe attrs) Q := by
  unfold observe setDeviceWith
  simp only [branch_factor,bind_assoc,pure_bind]
  cases flags : attrs.flags <;>
    simp only [flags,Option.isSome_none,Option.isSome_some,Option.getD_none,Option.getD_some,
      Bool.false_eq_true,ite_false,ite_true] at next ⊢
  all_goals
    repeat' first
      | (maintenance_head accepted; exact next)
      | (maintenance_head Pure.pure; exact early _)
      | (maintenance_head mark; exact marks _ _)
      | (maintenance_lift_action_head lookupInterface; exact lookup)
      | (maintenance_lift_action_head getDev; exact read)
      | (maintenance_lift_action_head invariant; exact bad)
      | (maintenance_lift_action_head orM; exact or _ _ _ _)
      | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind)
      | (maintenance_intro; try dsimp only)
      | split

theorem observe_prelude (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient) :
    StatePrefixEnsures (fun h w _ => h = [] ∧ w = initial)
      (PreludeSafe attrs (Campaign2.snapshot initial a).wg) (observe attrs)
      (fun _ h w _ => PreludePost attrs initial a h w) := by
  apply observe_entry_rule attrs
  · exact fun ret => prelude_pure attrs initial a ret
  · exact fun site value => prelude_mark attrs initial a site value
  · exact prelude_quiet attrs initial a _
      (Leanux.Proofs.Framing.lookupInterface_sameWGWorld _)
  · exact prelude_quiet attrs initial a _ Internal.getDev_frame
  · exact prelude_quiet attrs initial a _ (Internal.ambient_frame _)
  · exact fun left right b c => prelude_quiet attrs initial a _
      (Internal.branch_or_frame left right b c)
  · exact StatePrefixEnsures.bind (entry_record attrs initial a)
      (fun _ => after_entry attrs initial a (update attrs (attrs.flags.getD 0))
        (updateLanguage attrs (attrs.flags.getD 0)) (update_conforms attrs (attrs.flags.getD 0)))

end Leanux.Proofs.WG.Config.RequestOrder
