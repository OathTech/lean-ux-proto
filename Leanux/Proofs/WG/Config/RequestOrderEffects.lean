import Leanux.Proofs.WG.Config.RequestOrderModel

/-! Pure ordering and receipt-position consequences of the request languages. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

theorem PeerPrefix.append {xs middle rest : List PeerEntry} {left right : List Receipt}
    (first : PeerPrefix xs middle left) (second : PeerPrefix middle rest right) :
    PeerPrefix xs rest (left ++ right) := by
  induction first with
  | nil => exact second
  | cons kind positive tail ih => exact .cons kind positive (ih second)

theorem PeerPrefix.input {xs rest : List PeerEntry} {rs : List Receipt}
    (h : PeerPrefix xs rest rs) :
    xs = rs.map peerEntry ++ rest ∧ ∀ r ∈ rs, 0 ≤ r.result := by
  induction h with
  | nil xs => exact ⟨rfl, by simp⟩
  | cons kind positive tail ih =>
    refine ⟨?_, ?_⟩
    · simpa only [List.map_cons, List.cons_append, peerEntry, kind] using
        congrArg (List.cons _) ih.1
    · intro r member
      rcases List.mem_cons.mp member with equal | later
      · subst r; exact positive
      · exact ih.2 r later

theorem PeerFinished.prefixes {xs : List PeerEntry} {rs : List Receipt} {ret : Int}
    (h : PeerFinished xs rs ret) : PeerPartial xs rs := by
  rcases h with ⟨_,done⟩ | ⟨_,tail,done⟩ | ⟨before,p,tail,r,done,kind,neg,eq,_⟩
  · exact Or.inl ⟨[],done⟩
  · exact Or.inl ⟨.malformed :: tail,done⟩
  · exact Or.inr ⟨before,p,tail,r,done,kind,neg,eq⟩

theorem PeerAt.safe {xs rest : List PeerEntry} {h0 h : List Receipt}
    {out : Option Int × Unit} (point : PeerAt xs rest h0 out h) : PeerSafe xs h0 h := by
  obtain ⟨_,rs,eq,path⟩ := point
  exact ⟨rs,eq,Or.inl ⟨rest,path⟩⟩

theorem PeerDone.safe {xs : List PeerEntry} {h0 h : List Receipt}
    {out : Option Int × Unit} (done : PeerDone xs h0 out h) : PeerSafe xs h0 h := by
  obtain ⟨rs,eq,finish⟩ := done
  refine ⟨rs,eq,?_⟩
  cases result : out.1 with
  | none => exact Or.inl ⟨[],by simpa only [result] using finish⟩
  | some ret => exact (show PeerFinished xs rs ret by simpa only [result] using finish).prefixes

theorem AfterPeer.safe {xs rest : List PeerEntry} {p : PeerAttrs}
    {h0 h : List Receipt} {ret : Int} (point : AfterPeer xs p rest h0 ret h) :
    PeerSafe xs h0 h := by
  obtain ⟨prior,r,eq,path,kind,result⟩ := point
  refine ⟨prior ++ [r],eq,?_⟩
  by_cases neg : r.result < 0
  · exact Or.inr ⟨prior,p,rest,r,path,kind,neg,rfl⟩
  · exact Or.inl ⟨rest,path.append (.cons kind (by omega) (.nil rest))⟩

theorem AfterPeer.negative {xs rest : List PeerEntry} {p : PeerAttrs}
    {h0 h : List Receipt} {ret : Int} (point : AfterPeer xs p rest h0 ret h)
    (negative : ret < 0) : PeerDone xs h0 (some ret,()) h := by
  obtain ⟨prior,r,eq,path,kind,result⟩ := point
  exact ⟨prior ++ [r],eq,Or.inr (Or.inr
    ⟨prior,p,rest,r,path,kind,by omega,rfl,result.symm⟩)⟩

theorem AfterPeer.nonnegative {xs rest : List PeerEntry} {p : PeerAttrs}
    {h0 h : List Receipt} {ret : Int} (point : AfterPeer xs p rest h0 ret h)
    (nonnegative : ¬ret < 0) : PeerAt xs rest h0 (none,()) h := by
  obtain ⟨prior,r,eq,path,kind,result⟩ := point
  exact ⟨rfl,prior ++ [r],eq,
    path.append (.cons kind (by omega) (.nil rest))⟩

theorem keyed_empty (attrs : DeviceAttrs) : (keyedLanguage attrs).prefixes [] :=
  Or.inl (Or.inl rfl)

theorem afterPort_empty (attrs : DeviceAttrs) (flags : UInt32) :
    (afterPortLanguage attrs flags).prefixes [] := by
  unfold afterPortLanguage
  split
  · exact Or.inl (Or.inl rfl)
  · exact keyed_empty attrs

theorem afterFwmark_empty (attrs : DeviceAttrs) (flags : UInt32) :
    (afterFwmarkLanguage attrs flags).prefixes [] := by
  unfold afterFwmarkLanguage
  split
  · exact Or.inl (Or.inl rfl)
  · exact afterPort_empty attrs flags

theorem ClearPrefix.empty (attrs : DeviceAttrs) : ClearPrefix attrs [] := ⟨by simp,fun _ => rfl⟩

theorem ClearPrefix.append {attrs : DeviceAttrs} {l r : List Receipt}
    (hl : ClearPrefix attrs l) (hr : ClearPrefix attrs r) : ClearPrefix attrs (l ++ r) := by
  constructor
  · intro e member
    rcases List.mem_append.mp member with left | right
    · exact hl.1 e left
    · exact hr.1 e right
  · intro absent
    simp only [hl.2 absent,hr.2 absent,List.nil_append]

theorem ClearPrefix.singleton {attrs : DeviceAttrs} {pid : PeerId} {r : Receipt}
    (present : attrs.fwmark.isSome = true) (kind : r.kind = .clearSource pid) :
    ClearPrefix attrs [r] := by
  constructor
  · intro e member
    have same := List.mem_singleton.mp member
    subst e
    exact ⟨pid,kind⟩
  · intro missing
    simp only [present,Bool.true_eq_false] at missing

theorem update_empty (attrs : DeviceAttrs) (flags : UInt32) :
    (updateLanguage attrs flags).prefixes [] := Or.inl (ClearPrefix.empty attrs)

theorem request_empty (attrs : DeviceAttrs) : (requestLanguage attrs).prefixes [] :=
  Or.inl (Or.inl rfl)

theorem peerReceipts_append (l r : List Receipt) :
    peerReceipts (l ++ r) = peerReceipts l ++ peerReceipts r := List.filter_append _ _

theorem PeerPrefix.peerReceipts {xs rest : List PeerEntry} {rs : List Receipt}
    (path : PeerPrefix xs rest rs) : peerReceipts rs = rs := by
  induction path with
  | nil => rfl
  | cons kind positive tail ih =>
    simp only [RequestOrder.peerReceipts,List.filter_cons,kind,ite_true]
    exact congrArg (List.cons _) ih

theorem PeerPartial.peerReceipts {xs : List PeerEntry} {rs : List Receipt}
    (path : PeerPartial xs rs) : peerReceipts rs = rs := by
  rcases path with ⟨_,path⟩ | ⟨before,p,tail,r,path,kind,neg,rfl⟩
  · exact path.peerReceipts
  · rw [peerReceipts_append,path.peerReceipts]
    simp only [RequestOrder.peerReceipts,List.filter_cons,kind,ite_true,List.filter_nil]

theorem PeerPartial.input {xs : List PeerEntry} {rs : List Receipt}
    (path : PeerPartial xs rs) : ∃ rest, xs = rs.map peerEntry ++ rest := by
  rcases path with ⟨rest,path⟩ | ⟨before,p,tail,r,path,kind,neg,rfl⟩
  · exact ⟨rest,path.input.1⟩
  · refine ⟨tail,?_⟩
    simpa only [List.map_append,List.map_cons,List.map_nil,peerEntry,kind,
      List.append_assoc,List.cons_append,List.nil_append] using path.input.1

theorem PeerPartial.negative_last {xs : List PeerEntry} {rs : List Receipt} {r : Receipt}
    (path : PeerPartial xs rs) (member : r ∈ rs) (negative : r.result < 0) :
    ∃ before, rs = before ++ [r] := by
  rcases path with ⟨_,path⟩ | ⟨before,p,tail,last,path,kind,neg,rfl⟩
  · have positive := path.input.2 r member
    omega
  · rcases List.mem_append.mp member with prior | final
    · have positive := path.input.2 r prior
      omega
    · have same := List.mem_singleton.mp final
      subst r
      exact ⟨before,rfl⟩

theorem event_peerSilent (kind : Kind)
    (silent : ∀ p, kind ≠ .peer p) : PeerSilent (Language.event kind) := by
  have one {r : Receipt} (hk : r.kind = kind) : peerReceipts [r] = [] := by
    cases eq : kind <;> simp_all [peerReceipts]
  constructor
  · intro h path
    rcases path with rfl | ⟨r,rfl,kind⟩
    · rfl
    · exact one kind
  · intro _ _ path
    obtain ⟨r,rfl,kind,_⟩ := path
    exact one kind

theorem returning_peerOrdered (attrs : DeviceAttrs) {α : Type} (x : α) :
    PeerOrdered attrs (Language.returning x) := by
  intro _ path
  subst_vars
  exact Or.inl ⟨attrs.peers.getD [],.nil _⟩

theorem bind_peerOrdered (attrs : DeviceAttrs) {α β : Type}
    (A : Language α) (B : α → Language β) (silent : PeerSilent A)
    (ordered : ∀ x, PeerOrdered attrs (B x)) : PeerOrdered attrs (A.bind B) := by
  intro h path
  rcases path with first | ⟨x,l,r,hl,hr,rfl⟩
  · rw [silent.1 h first]
    exact Or.inl ⟨attrs.peers.getD [],.nil _⟩
  · simpa only [peerReceipts_append,silent.2 x l hl,List.nil_append] using ordered x r hr

theorem keyed_peerOrdered (attrs : DeviceAttrs) : PeerOrdered attrs (keyedLanguage attrs) := by
  apply bind_peerOrdered attrs _ _ (event_peerSilent _ (fun _ => by intro equality; cases equality))
  intro _ h path
  change PeerPartial (attrs.peers.getD []) h at path
  simpa only [path.peerReceipts] using path

theorem afterPort_peerOrdered (attrs : DeviceAttrs) (flags : UInt32) :
    PeerOrdered attrs (afterPortLanguage attrs flags) := by
  unfold afterPortLanguage
  split
  · exact bind_peerOrdered attrs _ _ (event_peerSilent _ (fun _ => by intro equality; cases equality))
      (fun _ => keyed_peerOrdered attrs)
  · exact keyed_peerOrdered attrs

theorem afterFwmark_peerOrdered (attrs : DeviceAttrs) (flags : UInt32) :
    PeerOrdered attrs (afterFwmarkLanguage attrs flags) := by
  unfold afterFwmarkLanguage
  split
  · apply bind_peerOrdered attrs _ _ (event_peerSilent _ (fun _ => by intro equality; cases equality))
    intro ret
    split
    · exact returning_peerOrdered attrs ret
    · exact afterPort_peerOrdered attrs flags
  · exact afterPort_peerOrdered attrs flags

theorem ClearPrefix.peerReceipts {attrs : DeviceAttrs} {h : List Receipt}
    (path : ClearPrefix attrs h) : peerReceipts h = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro r member
  obtain ⟨pid,kind⟩ := path.1 r member
  simp only [kind,Bool.false_eq_true,not_false_eq_true]

theorem update_peerOrdered (attrs : DeviceAttrs) (flags : UInt32) :
    PeerOrdered attrs (updateLanguage attrs flags) :=
  bind_peerOrdered attrs _ _ ⟨fun _ h => h.peerReceipts,fun _ _ h => h.peerReceipts⟩
    (fun _ => afterFwmark_peerOrdered attrs flags)

theorem request_peerOrdered (attrs : DeviceAttrs) :
    PeerOrdered attrs (requestLanguage attrs) :=
  bind_peerOrdered attrs _ _ (event_peerSilent _ (fun _ => by intro equality; cases equality))
    (fun _ => update_peerOrdered attrs _)

theorem request_peer_position (attrs : DeviceAttrs) (h : List Receipt)
    (path : (requestLanguage attrs).prefixes h) (i : Nat) (r : Receipt) (p : PeerAttrs)
    (selected : (peerReceipts h)[i]? = some r) (kind : r.kind = .peer p) :
    (attrs.peers.getD [])[i]? = some (.attrs p) := by
  obtain ⟨rest,shape⟩ := (request_peerOrdered attrs h path).input
  rw [shape,List.getElem?_append_left]
  · simp only [List.getElem?_map,selected,Option.map_some,peerEntry,kind]
  · have lt : i < (peerReceipts h).length := by
      exact (List.getElem?_eq_some_iff.mp selected).1
    simpa only [List.length_map] using lt

theorem request_negative_peer_last (attrs : DeviceAttrs) (h : List Receipt)
    (path : (requestLanguage attrs).prefixes h) (r : Receipt)
    (member : r ∈ peerReceipts h) (negative : r.result < 0) :
    ∃ before, peerReceipts h = before ++ [r] :=
  (request_peerOrdered attrs h path).negative_last member negative

theorem Begun.append {attrs : DeviceAttrs} {initial : Campaign2.State}
    {h : List Receipt} (point : Begun attrs initial h) (tail : List Receipt) :
    Begun attrs initial (h ++ tail) := by
  obtain ⟨r,rest,rfl,effect⟩ := point
  exact ⟨r,rest ++ tail,rfl,effect⟩

theorem request_normal_stages (attrs : DeviceAttrs) (ret : Int) (h : List Receipt)
    (path : (requestLanguage attrs).normal ret h) :
    h = [] ∨ ∃ entry clears rest,
      entry.kind = .updateEntry (attrs.flags.getD 0) ∧ ClearPrefix attrs clears ∧
        h = entry :: (clears ++ rest) ∧ (afterFwmarkLanguage attrs (attrs.flags.getD 0)).normal ret rest := by
  rcases path with empty | ⟨_,first,rest,firstPath,restPath,shape⟩
  · exact Or.inl empty
  · obtain ⟨entry,rfl,kind,_⟩ := firstPath
    obtain ⟨_,clears,tail,clearPath,tailPath,rfl⟩ := restPath
    exact Or.inr ⟨entry,clears,tail,kind,clearPath,shape,tailPath⟩

theorem afterFwmark_normal_port (attrs : DeviceAttrs) (flags : UInt32) (ret : Int)
    (h : List Receipt) (present : attrs.listenPort.isSome = true)
    (path : (afterFwmarkLanguage attrs flags).normal ret h) :
    ∃ r tail, h = r :: tail ∧ r.kind = .port (attrs.listenPort.getD 0) ∧
      (r.result ≠ 0 → tail = [] ∧ ret = r.result) := by
  simp only [afterFwmarkLanguage,present,ite_true,Language.bind] at path
  obtain ⟨port,l,tail,head,rest,rfl⟩ := path
  obtain ⟨r,rfl,kind,result⟩ := head
  refine ⟨r,tail,rfl,kind,?_⟩
  intro nonzero
  have nz : port != 0 := by simpa only [← result,bne_iff_ne] using nonzero
  simp only [nz,ite_true,Language.returning] at rest
  exact ⟨rest.2,rest.1.trans result.symm⟩

theorem request_normal_port_cutoff (attrs : DeviceAttrs) (ret : Int) (h : List Receipt)
    (present : attrs.listenPort.isSome = true) (nonempty : h ≠ [])
    (path : (requestLanguage attrs).normal ret h) :
    ∃ entry clears r tail,
      entry.kind = .updateEntry (attrs.flags.getD 0) ∧ ClearPrefix attrs clears ∧
      r.kind = .port (attrs.listenPort.getD 0) ∧ h = entry :: (clears ++ r :: tail) ∧
      (r.result ≠ 0 → tail = [] ∧ ret = r.result) := by
  rcases request_normal_stages attrs ret h path with empty |
    ⟨entry,clears,rest,kind,clearPath,shape,next⟩
  · exact False.elim (nonempty empty)
  · obtain ⟨r,tail,rfl,port,cut⟩ := afterFwmark_normal_port attrs _ ret rest present next
    exact ⟨entry,clears,r,tail,kind,clearPath,port,shape,cut⟩

end Leanux.Proofs.WG.Config.RequestOrder
