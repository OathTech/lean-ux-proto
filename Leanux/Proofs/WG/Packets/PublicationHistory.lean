import Leanux.Proofs.WG.Origins.OwnerPrepare

/-! A live crypted packet is anchored to a specified decrypt occurrence in
this same journal, its actual successful publication, and the retained concrete
packet/peer certificate. This is the state invariant still needed between
publication and later consumption; no whole-run preservation is asserted. -/
namespace Leanux.Proofs.WG.PublicationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity
open Origins.HistorySupport (sessions)
variable {id : SkbId}

/-- The strict earlier prefix stays fixed when later events are appended.
The selected peer may be absent; normal consume recovers residency itself. -/
def Anchored (h : List RxHistory.Event) (id : SkbId) (w : WGWorld) : Prop :=
  ∃ pre post, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
    h = pre ++ .rx (.decrypt id r) :: post ∧
    Published id r out pid published ambient ∧
    Retained (sessions pre) id r out pid published w

def Inv (h : List RxHistory.Event) (w : WGWorld) : Prop :=
  ∀ id pkt, (RxDisposition.nativeRxStore w).2 id = some pkt →
    pkt.state = .crypted → Anchored h id w

theorem Anchored.append (hi : Anchored h id w) (suffix : List RxHistory.Event) :
    Anchored (h ++ suffix) id w := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,source,retained⟩ := hi
  exact ⟨pre,post ++ suffix,r,out,pid,published,ambient,
    by simp only [position,List.append_assoc,List.cons_append],source,retained⟩

theorem Inv.append (hi : Inv h w) (suffix : List RxHistory.Event) : Inv (h ++ suffix) w :=
  fun id pkt hp hs => (hi id pkt hp hs).append suffix

theorem Inv.no_crypted (h : List RxHistory.Event) (w : WGWorld)
    (empty : ∀ id pkt, (RxDisposition.nativeRxStore w).2 id = some pkt → pkt.state ≠ .crypted) :
    Inv h w := fun id pkt hp hs => False.elim (empty id pkt hp hs)

/-- The actual initial fixture has no RX packet cells, for either flag. -/
theorem initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  have hd := congrArg WGStoreView.dev hw
  change w.dev = (if net && !bare then some {ifindex := 3,ifname := "wg0"} else none) at hd
  apply Inv.no_crypted
  intro id pkt hp
  unfold RxDisposition.nativeRxStore at hp
  rw [hd] at hp
  split at hp <;> simp at hp

/-- Pointwise concrete field transport permits unrelated packet writes and
peer changes, including disappearance of the selected peer. -/
theorem Anchored.transport (hi : Anchored h id w)
    (stamp : packetStamp v id = packetStamp w id)
    (packet : (RxDisposition.nativeRxStore v).2 id = (RxDisposition.nativeRxStore w).2 id)
    (peers : ∀ (pid : PeerId) (d : Device) (p : Peer), v.dev = some d → d.peers[pid]? = some p →
      ∃ old q, w.dev = some old ∧ old.peers[pid]? = some q ∧
        CurrentIdentity.identity p = CurrentIdentity.identity q) :
    Anchored h id v := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,source,retained⟩ := hi
  exact ⟨pre,post,r,out,pid,published,ambient,position,source,
    retained.transport stamp packet (peers pid)⟩

/-- Every surviving crypted cell must keep its exact packet and stamp. These
are concrete state-change obligations, not certificate or history premises. -/
theorem Inv.transport (hi : Inv h w)
    (packets : ∀ id pkt, (RxDisposition.nativeRxStore v).2 id = some pkt → pkt.state = .crypted →
      (RxDisposition.nativeRxStore w).2 id = some pkt ∧ packetStamp v id = packetStamp w id)
    (peers : ∀ (pid : PeerId) (d : Device) (p : Peer), v.dev = some d → d.peers[pid]? = some p →
      ∃ old q, w.dev = some old ∧ old.peers[pid]? = some q ∧
        CurrentIdentity.identity p = CurrentIdentity.identity q) : Inv h v := by
  intro id pkt hv crypted
  obtain ⟨hw,stamp⟩ := packets id pkt hv crypted
  exact (hi id pkt hw crypted).transport stamp (hv.trans hw.symm) peers

/-- The checked entry of this exact historical decrypt and its actual normal
publication establish the anchor at the real publication endpoint. -/
theorem anchored_publication (safe : OwnerChecks.Safe h)
    (position : h = pre ++ .rx (.decrypt id r) :: post)
    (published : Published id r out pid v ambient) : Anchored h id v := by
  exact ⟨pre,post,r,out,pid,v,ambient,position,published,
    (OwnerChecks.Safe.published safe position published).live.retained⟩

/-- Receipt truth comes from the actual R4 source link; the certificate uses
the same retained packet and its strict earlier decrypt/session occurrence.
No receiving-key validity or post-consume residency is required. -/
theorem Inv.receipt {receipt : RxDisposition.ConsumeReceipt} (hi : Inv h receipt.run.before)
    (source : RxLink.Source id stamp receipt) (crypted : receipt.packet.state = .crypted) :
    ∃ pre post, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      h = pre ++ .rx (.decrypt id r) :: post ∧
      Published id r out pid published ambient ∧
      ConsumeCertificate (sessions pre) id r out pid published stamp receipt := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,hpub,retained⟩ :=
    hi id receipt.packet source.2.1.2 crypted
  exact ⟨pre,post,r,out,pid,published,ambient,position,hpub,retained_receipt retained source⟩

end Leanux.Proofs.WG.PublicationHistory
