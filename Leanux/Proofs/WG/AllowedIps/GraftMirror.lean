import Leanux.Proofs.WG.AllowedIps.ChildMutation
import Leanux.Proofs.WG.AllowedIps.ListsMirror

/-! Original selected-root grafts, retaining both allocation refusals and the
source's intermediate writes. A missing allocation record remains a Stop. -/
set_option pp.structureInstances false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

theorem commonBits_wp (k : Kernel) (n : WG.AipNode) (key width : Nat)
    (hw : width = 32 ∨ width = 128) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.commonBits n key width
    ⦃⇓ x w => ⌜x = common width n.bits key ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w h
  exact ⟨_, _, commonBits_run n key width w hw, rfl, (commonRecords_k ..).trans h⟩

theorem freeNode_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d) (id : Nat) (n : WG.AipNode) (hn : d.nodes[id]? = some n) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.freeNode id
    ⦃⇓ x w => ⌜x = () ∧ w.k = { k with wg := some { d with nodes := d.nodes.erase id } }⌝⦄ := by
  have hg := getNode_wp k d id n hd hn
  mvcgen [WG.freeNode, hg, WG.modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem chooseAndConnectNode_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (parent id : Nat) (pn n : WG.AipNode) (hp : d.nodes[parent]? = some pn)
    (hn : d.nodes[id]? = some n) (hne : id ≠ parent) (hc : pn.cidr < pn.bitlen) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.chooseAndConnectNode parent id
    ⦃⇓ x w => ⌜x = () ∧ w.k = { k with wg := some (connectedChild d parent (bit pn.bitlen pn.cidr n.bits) id pn n) }⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  let side := bit pn.bitlen pn.cidr n.bits
  have hb : ¬ side > 1 := by have := bit_lt_two pn.bitlen pn.cidr n.bits; omega
  refine ⟨(), { w with k := { k with wg := some (connectedChild d parent side id pn n) } }, ?_, rfl, rfl⟩
  simp [WG.chooseAndConnectNode, WG.getNode, WG.getDev, getK, WG.choose,
    WG.connectNode, WG.setNode, WG.modifyDev, modifyK, WG.slotSet, hkw, hd, hp, hn,
    show ¬ pn.cidr ≥ pn.bitlen from by omega, Std.TreeMap.getElem?_insert, hne,
    side, bit, connectedChild] at hb ⊢
  simp only [show ¬ 1 < n.bits / 2 ^ (pn.bitlen - 1 - pn.cidr) % 2 from by omega, ↓reduceIte]
  rfl

theorem PlacementWitness.root_stopped_result {n : NodeData} {l r : Tree}
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr key))
    (h : PlacementWitness (.node n l r) width key cidr result) : result = (none, false) := by
  obtain ⟨c, u, ht, hf, he⟩ := h
  cases c with
  | here =>
    change Tree.node n l r = u at ht
    subst u
    rcases he with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨hc, hm, _⟩
    · exact he
    · exact he
    · exact False.elim (hstop ⟨by omega, hm⟩)
  | left m c right =>
    have hn := (Tree.node.inj ht).1
    subst m
    exact False.elim (hstop ⟨by have := hf.1; omega, hf.2.1⟩)
  | right m left c =>
    have hn := (Tree.node.inj ht).1
    subst m
    exact False.elim (hstop ⟨by have := hf.1; omega, hf.2.1⟩)

theorem nodePlacement_root_stopped_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (width key cidr : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hc : cidr ≤ width) (base : WG.Slot) (n : NodeData) (l r : Tree)
    (hr : RepAt d.nodes width base (.node n l r)) (hv : (Tree.node n l r).Valid width)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr key)) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.nodePlacement (some n.id) key cidr width
    ⦃⇓ x w => ⌜x = (none, false) ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  obtain ⟨x, v, he, hf, hp⟩ := nodePlacement_run w d width key cidr hw hk hc
    (hkw ▸ hd) (.node n l r) base hr hv
  exact ⟨x, v, he, hp.root_stopped_result hstop, hf.trans hkw⟩

def graftListed (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  { allocated d (WG.newNode addr cidr width (some pid)) with
    peers := d.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }

def connectedRoot (d : WG.Device) (v4 : Bool) (id : Nat) (n : WG.AipNode) : WG.Device :=
  rootWrite { d with nodes := d.nodes.insert id { n with parent := rootSlot v4 } } v4 (some id)

def graftOne (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let side := bit (rootWidth v4) cidr old.bits
  let attached := connectedChild (graftListed d (rootWidth v4) addr cidr pid p)
    d.nextNode side id leaf old
  connectedRoot attached v4 d.nextNode { leaf with bit := leaf.bit.set! side (some id) }

def graftTwo (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid split : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let mid := WG.newNode addr split (rootWidth v4) none
  let sd := bit (rootWidth v4) split old.bits
  let sn := bit (rootWidth v4) split addr
  let a := allocated (graftListed d (rootWidth v4) addr cidr pid p) mid
  let b := connectedChild a (d.nextNode + 1) sd id mid old
  let mid' := { mid with bit := mid.bit.set! sd (some id) }
  let c := connectedChild b (d.nextNode + 1) sn d.nextNode mid' leaf
  connectedRoot c v4 (d.nextNode + 1) { mid' with bit := mid'.bit.set! sn (some d.nextNode) }

def graftRolledBack (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let dl := unlisted (graftListed d width addr cidr pid p) d.nextNode
  { dl with nodes := dl.nodes.erase d.nextNode }

def graftInstalled (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let split := min cidr (common (rootWidth v4) old.bits addr)
  if split = cidr then graftOne d v4 id old addr cidr pid p
  else graftTwo d v4 id old addr cidr pid split p


theorem add_placed_root_graft_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hn : d.nodes[id]? = some old)
    (hroot : rootValue d v4 = some id) (hid : id < d.nextNode)
    (hc : cidr ≤ rootWidth v4)
    (hs : min cidr (common (rootWidth v4) old.bits addr) < rootWidth v4)
    (hplacement : ⦃fun w => ⌜w.k = k⌝⦄ WG.nodePlacement (some id) addr cidr (rootWidth v4)
      ⦃⇓ x w => ⌜x = (none, false) ∧ w.k = k⌝⦄) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) old.bits addr) ≠ cidr ∧
        w.k = { k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w.k = { k with wg := some (graftInstalled d v4 id old addr cidr pid p) })⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hgetRoot := slotGet_root_wp k d hd v4
  simp only [hroot] at hgetRoot
  have halloc := allocNode_wp k d hd .allocNode205 (WG.newNode addr cidr (rootWidth v4) (some pid))
  mvcgen [WG.add, branchCmp, branch, hgetRoot, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  all_goals try omega
  obtain ⟨hptr, hframe⟩ := (show _ = some id ∧ _ = k from by assumption)
  cases hptr
  mvcgen [hplacement, branch, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  obtain ⟨hplaced, hplacedFrame⟩ := (show _ = (none, false) ∧ _ = k from by assumption)
  cases hplaced
  mvcgen [halloc, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  obtain ⟨hnew, hak⟩ := (show _ = d.nextNode ∧ _ = { k with wg := some (allocated d (WG.newNode addr cidr (rootWidth v4) (some pid))) } from by assumption)
  cases hnew
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let da := allocated d leaf
  let ka : Kernel := { k with wg := some da }
  have hlist := listAddTail_wp ka da rfl pid d.nextNode p hp
  mvcgen [hlist, branch, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  intro hlisted
  let dl := graftListed d (rootWidth v4) addr cidr pid p
  let kl : Kernel := { k with wg := some dl }
  change _ = kl at hlisted
  have hrl : rootValue dl v4 = some id := hroot
  have hgl := slotGet_root_wp kl dl rfl v4
  simp only [hrl] at hgl
  mvcgen [hgl, invariant]
  all_goals try exact hlisted
  all_goals try dsimp only at *
  all_goals try simp_all
  obtain ⟨hdown, hrootFrame⟩ := (show _ = id ∧ _ = kl from by assumption)
  cases hdown
  have hne : d.nextNode ≠ id := Nat.ne_of_gt hid
  have hnl : dl.nodes[id]? = some old := by
    simp [dl, graftListed, allocated, Std.TreeMap.getElem?_insert, hne, hn]
  have hg := getNode_wp kl dl id old rfl hnl
  mvcgen [hg]
  all_goals try exact hrootFrame
  rename_i gotOld
  intro currentOld hold holdFrame
  cases hold
  have hcommon := commonBits_wp kl old addr (rootWidth v4) hw
  mvcgen [hcommon]
  all_goals try exact holdFrame
  rename_i gotCommon
  intro currentCommon hcommonValue hcommonFrame
  cases hcommonValue
  have hleaf : dl.nodes[d.nextNode]? = some leaf := by simp [dl, graftListed, allocated, leaf]
  have hglf := getNode_wp kl dl d.nextNode leaf rfl hleaf
  mvcgen [hglf]
  all_goals try exact hcommonFrame
  all_goals try exact (show _ = leaf ∧ _ = kl from by assumption).2
  all_goals obtain ⟨hleafValue, hleafFrame⟩ := (show _ = leaf ∧ _ = kl from by assumption)
  all_goals cases hleafValue
  all_goals try dsimp only [leaf, WG.newNode] at *
  all_goals try
    obtain ⟨hprev, hprevFrame⟩ := (show _ = leaf ∧ _ = kl from by assumption)
    cases hprev
  all_goals try dsimp only [leaf, WG.newNode] at *
  · have he : min cidr (common (rootWidth v4) old.bits addr) = cidr := by grind
    have hconn := chooseAndConnectNode_wp kl dl rfl d.nextNode id leaf old hleaf hnl
      (Ne.symm hne) (by change cidr < rootWidth v4; omega)
    mvcgen [hconn]
    all_goals try exact hleafFrame
    rename_i ignoredConn
    have hconnFrame := ignoredConn.2
    let side := bit (rootWidth v4) cidr old.bits
    let dc := connectedChild dl d.nextNode side id leaf old
    let kc : Kernel := { k with wg := some dc }
    have hnc : dc.nodes[d.nextNode]? = some { leaf with bit := leaf.bit.set! side (some id) } := by
      simp [dc, connectedChild]
    have hconnect := connectNode_root_wp kc dc rfl v4 d.nextNode _ hnc
    mvcgen [branch, hconnect]
    all_goals try exact hconnFrame
    intro hfinished
    refine Or.inr (Or.inr ⟨trivial, ?_⟩)
    simpa only [graftInstalled, if_pos he, graftOne, connectedRoot] using hfinished
  · have he : min cidr (common (rootWidth v4) old.bits addr) ≠ cidr := by grind
    let split := min cidr (common (rootWidth v4) old.bits addr)
    let mid := WG.newNode addr split (rootWidth v4) none
    have halloc2 := allocNode_wp kl dl rfl .allocNode234 mid
    simp only [mid, WG.newNode] at halloc2
    mvcgen [halloc2, branch, invariant]
    all_goals try exact hleafFrame
    all_goals try dsimp only at *
    all_goals try simp_all
    · rename_i hNoFrame
      have hdel := listDel_wp kl dl rfl d.nextNode
      mvcgen [hdel]
      all_goals try exact hNoFrame
      rename_i ignored
      intro currentDel hdelFrame
      let dr := unlisted dl d.nextNode
      let kr : Kernel := { k with wg := some dr }
      have hnr : dr.nodes[d.nextNode]? = some leaf := hleaf
      have hfree := freeNode_wp kr dr rfl d.nextNode leaf hnr
      mvcgen [hfree]
      all_goals try dsimp +zetaDelta only at *
      all_goals simp_all [graftRolledBack, he]
    · let mid := WG.newNode addr split (rootWidth v4) none
      obtain ⟨hmId, hYesFrame⟩ := (show _ = dl.nextNode ∧ _ = { kl with wg := some (allocated dl mid) } from by assumption)
      change _ = d.nextNode + 1 at hmId
      cases hmId
      simp only [show dl.nextNode = d.nextNode + 1 from rfl]
      let dm := allocated dl mid
      let km : Kernel := { k with wg := some dm }
      have hmid : dm.nodes[d.nextNode + 1]? = some mid := by simp [dm, allocated, dl, graftListed]
      have hne2 : d.nextNode + 1 ≠ id := Nat.ne_of_gt (Nat.lt_trans hid (Nat.lt_succ_self _))
      have hdown : dm.nodes[id]? = some old := by
        simp [dm, allocated, dl, graftListed, Std.TreeMap.getElem?_insert, hne, hn, hne2]
      have hconn1 := chooseAndConnectNode_wp km dm rfl (d.nextNode + 1) id mid old hmid hdown
        (Ne.symm hne2) hs
      mvcgen [hconn1]
      all_goals try exact hYesFrame
      rename_i ignored1
      intro currentConn1 hconn1Frame
      let sd := bit (rootWidth v4) split old.bits
      let sn := bit (rootWidth v4) split addr
      let mid' := { mid with bit := mid.bit.set! sd (some id) }
      let dc := connectedChild dm (d.nextNode + 1) sd id mid old
      let kc : Kernel := { k with wg := some dc }
      have hmid' : dc.nodes[d.nextNode + 1]? = some mid' := by simp [dc, connectedChild, mid']
      have hleaf' : dc.nodes[d.nextNode]? = some leaf := by
        simp [dc, connectedChild, dm, allocated, dl, graftListed, Std.TreeMap.getElem?_insert,
          Ne.symm hne, Nat.ne_of_gt (Nat.lt_succ_self d.nextNode), leaf, Std.TreeMap.getElem_insert]
      have hconn2 := chooseAndConnectNode_wp kc dc rfl (d.nextNode + 1) d.nextNode mid' leaf hmid' hleaf'
        (by omega) hs
      mvcgen [hconn2]
      all_goals try exact hconn1Frame
      rename_i ignored2
      intro hconn2Frame
      let sn := bit (rootWidth v4) split addr
      let db := connectedChild dc (d.nextNode + 1) sn d.nextNode mid' leaf
      let kb : Kernel := { k with wg := some db }
      have hmid'' : db.nodes[d.nextNode + 1]? = some { mid' with bit := mid'.bit.set! sn (some d.nextNode) } := by
        simp [db, connectedChild]
      have hfinal := connectNode_root_wp kb db rfl v4 (d.nextNode + 1) _ hmid''
      mvcgen [branch, hfinal]
      all_goals try exact hconn2Frame
      intro hfinished
      apply Or.inr
      apply Or.inr
      simpa only [graftInstalled, if_neg he, graftTwo, connectedRoot] using hfinished

end Leanux.Proofs.WG.AllowedIps
