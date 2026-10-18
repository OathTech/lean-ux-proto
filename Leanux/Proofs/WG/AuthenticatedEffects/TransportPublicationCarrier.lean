import Leanux.Proofs.WG.AuthenticatedEffects.TransportDriverSource

/-! A packet-level publication carrier for the shared driver. It retains the
actual successful decrypt/publication occurrence and immutable packet stamp,
without importing unrelated historical peer-identity obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
variable {id : SkbId}

def Anchor (h : List TransportDriver.OriginEvent) (id : SkbId) (pkt : RxPacket) (w : WGWorld) : Prop :=
  ∃ pre post, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
    h = pre ++ .receipt (.decrypt id r) :: post ∧
    Published id r out pid published ambient ∧ pkt = {out with state := .crypted} ∧
    packetStamp w id = packetStamp r.before id

def Inv (h : List TransportDriver.OriginEvent) (w : WGWorld) : Prop :=
  ∀ id pkt, (RxDisposition.nativeRxStore w).2 id = some pkt → pkt.state = .crypted → Anchor h id pkt w

theorem Anchor.append (hi : Anchor h id pkt w) (suffix : List TransportDriver.OriginEvent) :
    Anchor (h ++ suffix) id pkt w := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,valid,packet,stamp⟩ := hi
  exact ⟨pre,post ++ suffix,r,out,pid,published,ambient,
    by simp only [position,List.append_assoc,List.cons_append],valid,packet,stamp⟩

theorem Inv.append (hi : Inv h w) (suffix : List TransportDriver.OriginEvent) : Inv (h ++ suffix) w :=
  fun id pkt cell crypted => (hi id pkt cell crypted).append suffix

theorem Anchor.transport (hi : Anchor h id pkt w) (stamp : packetStamp v id = packetStamp w id) :
    Anchor h id pkt v := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,valid,packet,old⟩ := hi
  exact ⟨pre,post,r,out,pid,published,ambient,position,valid,packet,stamp.trans old⟩

theorem Inv.transport (hi : Inv h w)
    (cells : ∀ id pkt, (RxDisposition.nativeRxStore v).2 id = some pkt → pkt.state = .crypted →
      (RxDisposition.nativeRxStore w).2 id = some pkt ∧ packetStamp v id = packetStamp w id) : Inv h v := by
  intro id pkt cell crypted
  obtain ⟨old,stamp⟩ := cells id pkt cell crypted
  exact (hi id pkt old crypted).transport stamp

theorem initial (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  have hd := congrArg WGStoreView.dev same
  change w.dev = (if net && !bare then some {ifindex := 3,ifname := "wg0"} else none) at hd
  intro id pkt cell crypted
  unfold RxDisposition.nativeRxStore at cell
  rw [hd] at cell
  split at cell <;> simp at cell

theorem published_packet (id : SkbId) (r : WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : WGWorld) (ambient : Ambient)
    (published : Published id r out pid v ambient) :
    (RxDisposition.nativeRxStore v).2 id = some {out with state := .crypted} ∧
      packetStamp v id = packetStamp r.before id := by
  obtain ⟨run,output,checked,checkedAmbient,installed,installedAmbient,hbranch,hstore,hpub⟩ := published
  obtain ⟨d,k,hd,hp,hk,valid,decrypt,record,aead⟩ := RxOrigin.decrypt_receipt id r out run output
  have ka := decrypt_kernel _ _ _ _ _ _ decrypt
  have kb : checked = r.after := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .decWorkerDecrypted true) (fun g => g = r.after))
    r.after r.ambientAfter true checked checkedAmbient rfl hbranch
  have hchecked : checked.dev = some d := by simp [kb,ka,hd]
  rw [Packets.setRxSkb_run checked checkedAmbient d id r.value.1 (fun _ => out) hchecked hp] at hstore
  cases hstore
  obtain ⟨pubdev,pkt,key,p,hdev,hpkt,hkey,word,hpeer,effect⟩ := publish_execution _ _ _ _ _ _ _ hpub
  have ed : pubdev = {d with rxSkbs := d.rxSkbs.insert id out} := Option.some.inj
    (hdev.symm.trans (by simp [Packets.update,hchecked]))
  subst pubdev
  have eqpkt : pkt = out := by simpa using hpkt.symm
  subst pkt
  have hfinal := congrArg WGStoreView.dev effect
  change v.dev = some _ at hfinal
  constructor
  · simp [RxDisposition.nativeRxStore,hfinal]
  · simp [packetStamp,hfinal,hd]

theorem prepare_normal (w v : WGWorld) (a b : Ambient)
    (h t : List TransportDriver.OriginEvent) (value : Option PeerId)
    (hi : Inv h w) (run : runWGPrefix RxOrigin.prepare w a h = (.ok ((value,v),b),t)) : Inv t v := by
  cases value with
  | none =>
    obtain ⟨rfl,rfl⟩ := PublicationHistory.native_prepare_none w v a b h t run
    exact hi
  | some pid =>
    obtain ⟨selected,r,pre,tail,valid,position,frame,dead,published⟩ :=
      PublicationHistory.native_prepare_selected w v a b h t pid run
    intro id pkt cell crypted
    by_cases same : id = selected
    · subst id
      cases output : r.value.2 with
      | none =>
        obtain ⟨final,hfinal,hdead⟩ := dead output
        have packet : pkt = final := Option.some.inj (cell.symm.trans hfinal)
        subst pkt
        cases crypted.symm.trans hdead
      | some out =>
        have pub := published out output
        obtain ⟨stored,stamp⟩ := published_packet selected r out pid v b pub
        exact ⟨h ++ pre,tail,r,out,pid,v,b,by simpa only [List.append_assoc] using position,
          pub,Option.some.inj (cell.symm.trans stored),stamp⟩
    · have packet := congrFun (congrArg (fun s => s.2.1) frame) id
      have old : (RxDisposition.nativeRxStore w).2 id = some pkt := by
        simpa only [PublicationHistory.around,same,ite_false,cell] using packet.symm
      have stamp : packetStamp v id = packetStamp w id :=
        congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst frame)
      rw [position,List.append_assoc]
      exact ((hi id pkt old crypted).transport stamp).append (pre ++ .receipt (.decrypt selected r) :: tail)

theorem Anchor.authenticated (anchor : Anchor history id pkt w) :
    ∃ pre post, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      history = pre ++ .receipt (.decrypt id r) :: post ∧
      Published id r out pid published ambient ∧ pkt = {out with state := .crypted} ∧
      ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
        d.keypairs[r.value.1.keypair]? = some k ∧ k.receiving.isValid = true ∧
        pkt.keypair = r.value.1.keypair ∧ pkt.nonce = u64le r.value.1.bytes 8 ∧
        aeadDecrypt k.receiving.key (counterNonce pkt.nonce) (r.value.1.bytes.drop 16) [] = some pkt.bytes := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,pub,packet,stamp⟩ := anchor
  obtain ⟨d,k,hd,hp,hk,hvalid,_,record,aead⟩ := RxOrigin.decrypt_receipt id r out pub.1 pub.2.1
  have key : out.keypair = r.value.1.keypair := by
    have projected := congrArg RxPacket.keypair record
    exact projected
  have nonce : out.nonce = u64le r.value.1.bytes 8 := by
    have projected := congrArg RxPacket.nonce record
    exact projected
  have packetKey : pkt.keypair = out.keypair := by
    have projected := congrArg RxPacket.keypair packet
    exact projected
  have packetNonce : pkt.nonce = out.nonce := by
    have projected := congrArg RxPacket.nonce packet
    exact projected
  have bytes : pkt.bytes = out.bytes := by
    have projected := congrArg RxPacket.bytes packet
    exact projected
  refine ⟨pre,post,r,out,pid,published,ambient,position,pub,packet,d,k,hd,hp,hk,hvalid,?_,?_,?_⟩
  · exact packetKey.trans key
  · exact packetNonce.trans nonce
  · simpa only [packetNonce,nonce,bytes] using aead

/-- The shared native decrypt preparation preserves each crypted packet's actual
successful AEAD publication. A Stop keeps its precise observed prefix; only normal
returns expose a resulting WG world to which the packet invariant applies. -/
theorem native_prepare_preserves :
    StatePrefixPreserves (fun h w _ => Inv h w) (fun _ => True) RxOrigin.prepare := by
  intro w a h hi
  obtain ⟨suffix,appended⟩ := TransportDriver.native_prepare_appends w a h
  refine ⟨suffix,appended,True.intro,?_⟩
  cases result : (runPrefix (RxOrigin.prepare.run w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    exact prepare_normal w v a b h _ value hi (Prod.ext result rfl)

theorem prepare_preserves (record : TransportDriver.OriginEvent → E)
    (decode : E → Option TransportDriver.OriginEvent)
    (inverse : ∀ event, decode (record event) = some event) :
    PrefixPreserves (fun h w => Inv (h.filterMap decode) w.wg) (fun _ => True)
      (TransportDriver.prepare record decode) :=
  native_prepare_preserves.liftWGObserver.focus record decode inverse

end Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication
