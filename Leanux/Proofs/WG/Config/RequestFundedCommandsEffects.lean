import Leanux.Proofs.WG.Config.RequestFundedCommandsModel
import Leanux.Proofs.WG.Config.RequestOrderEffects
import Leanux.Proofs.WG.AllowedIps.RoutingRetains

/-! Pure request-language and represented-table consequences. A completed peer receipt requires a prior completed key stage; canonical flat tables come from represented trees. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
open Leanux Leanux.WG Queues Queues.RxCredits AllowedIps Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration

theorem KeyOrEmpty.prepend {left right : List Receipt}
    (silent : peerReceipts left=[]) (point : KeyOrEmpty right) :
    KeyOrEmpty (left++right) := by
  rcases point with empty|⟨key,member,kind⟩
  · exact Or.inl (by rw [peerReceipts_append,silent,empty];rfl)
  · exact Or.inr ⟨key,List.mem_append_right left member,kind⟩

theorem bind_keyOrEmpty {α β : Type} (A : Language α) (B : α→Language β)
    (silent : PeerSilent A)
    (next : ∀x h,(B x).prefixes h→KeyOrEmpty h)
    (h : List Receipt) (path : (A.bind B).prefixes h) : KeyOrEmpty h := by
  rcases path with first|⟨x,left,right,first,last,rfl⟩
  · exact Or.inl (silent.1 h first)
  · exact (next x right last).prepend (silent.2 x left first)

theorem keyed_keyOrEmpty (attrs : DeviceAttrs) (h : List Receipt)
    (path : (keyedLanguage attrs).prefixes h) : KeyOrEmpty h := by
  rcases path with first|⟨ret,left,right,first,_,rfl⟩
  · rcases first with rfl|⟨key,rfl,kind⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨key,by simp,kind⟩
  · obtain ⟨key,rfl,kind,_⟩:=first
    exact Or.inr ⟨key,by simp,kind⟩

theorem afterPort_keyOrEmpty (attrs : DeviceAttrs) (flags : UInt32) (h : List Receipt)
    (path : (afterPortLanguage attrs flags).prefixes h) : KeyOrEmpty h := by
  unfold afterPortLanguage at path
  split at path
  · exact bind_keyOrEmpty _ _
      (event_peerSilent _ (fun _=>by intro e;cases e))
      (fun _=>keyed_keyOrEmpty attrs) h path
  · exact keyed_keyOrEmpty attrs h path

theorem afterFwmark_keyOrEmpty (attrs : DeviceAttrs) (flags : UInt32) (h : List Receipt)
    (path : (afterFwmarkLanguage attrs flags).prefixes h) : KeyOrEmpty h := by
  unfold afterFwmarkLanguage at path
  split at path
  · apply bind_keyOrEmpty _ _ (event_peerSilent _ (fun _=>by intro e;cases e)) ?_ h path
    intro ret history next
    split at next
    · exact Or.inl (by rw [next];rfl)
    · exact afterPort_keyOrEmpty attrs flags history next
  · exact afterPort_keyOrEmpty attrs flags h path

theorem update_keyOrEmpty (attrs : DeviceAttrs) (flags : UInt32) (h : List Receipt)
    (path : (updateLanguage attrs flags).prefixes h) : KeyOrEmpty h :=
  bind_keyOrEmpty (Language.closed (α:=Unit) (ClearPrefix attrs)) _
    ⟨fun _ p=>p.peerReceipts,fun _ _ p=>p.peerReceipts⟩
    (fun _=>afterFwmark_keyOrEmpty attrs flags) h path

theorem request_keyOrEmpty (attrs : DeviceAttrs) (h : List Receipt)
    (path : (requestLanguage attrs).prefixes h) : KeyOrEmpty h :=
  bind_keyOrEmpty _ _ (event_peerSilent _ (fun _=>by intro e;cases e))
    (fun _=>update_keyOrEmpty attrs _) h path

theorem request_peer_shape (attrs : DeviceAttrs) (shape : DeviceAddressShape attrs)
    (h : List Receipt) (path : (requestLanguage attrs).prefixes h)
    (r : Receipt) (member : r∈peerReceipts h) :
    ∃p,r.kind=.peer p ∧ PeerAddressShape p := by
  have flag:=(List.mem_filter.mp member).2
  obtain ⟨p,kind⟩ : ∃p,r.kind=.peer p := by
    cases kind:r.kind <;> simp only [kind,Bool.false_eq_true] at flag
    exact ⟨_,rfl⟩
  obtain ⟨rest,input⟩:=(request_peerOrdered attrs h path).input
  refine ⟨p,kind,shape p ?_⟩
  rw [input]
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨r,member,by simp only [peerEntry,kind]⟩

theorem entry_routed (cs : Ledger) (loans : Reservations)
    (s : Campaign2.Snapshot) (pre : ProjectedEntry cs loans s) :
    ∃tables,RoutedView (s.wg.device.map routingState) tables := by
  obtain ⟨d,device,t4,t6,represented,_⟩:=pre.2
  exact ⟨(t4.bindings 32,t6.bindings 128),d,t4,t6,
    by simp only [device,Option.map_some],represented,fun _=>Iff.rfl,fun _=>Iff.rfl⟩

end Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
