import PairInsertCallFacts
import PairIndexExternal
import PairStackBytes
import RandomReadyCheck
import RandomService

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage

def providerPending (c : Context) : List Span :=
  if LookupPendingRead (c.preempt+512) then [(softirqPendingAddress.toNat,2)] else []

def providerProtected (n : Names) (o : Offsets) (c : Context) (s : MachineState) : List Span :=
  Index.storageSpans n o ++ Index.callStack s 135 true ++ Trie.callServices c ++ providerPending c

/-- Extra current-state resources for the actual random body. The 135-word
reservation comprises insertion's seven slots plus the provider's 1 KiB.
This does not constrain a returned value or a future source/binary path. -/
def providerCheck (n : Names) (o : Offsets) (c : Context) (s : MachineState)
    (ra : UInt64) (config : RandomProvider.Config) : Except String Unit := do
  Index.callFrameCheck n o c s ra 135
  unless s.data.system.cpl==0 && !s.data.system.bits[10] do throw "insert.provider.mode"
  let outer : Context := ⟨c.coverage,c.preempt+512⟩
  unless !decide outer.Needed || c.coverage.capacity.toNat>0 do throw "insert.provider.capacity"
  RandomProvider.check config c.coverage.task.toNat
    (RandomRecordingActive c.coverage (c.preempt+512)) s.data.dmem
  unless spansApart config.blocks (providerProtected n o c s) do throw "insert.provider.private-alias"
  unless spansApart (Index.callStack s 135 false) (providerPending c) do
    throw "insert.provider.pending-stack"

structure ProviderFacts (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (config : RandomProvider.Config) : Prop where
  wide : Index.CallFacts n o c initial ra 135
  privilege : initial.data.system.cpl=0
  direction : initial.data.system.bits[10]=false
  capacity : (Context.mk c.coverage (c.preempt+512)).Needed → 0<c.coverage.capacity.toNat
  privateCheck : RandomProvider.check config c.coverage.task.toNat
    (RandomRecordingActive c.coverage (c.preempt+512)) initial.data.dmem=.ok ()
  privateApart : spansApart config.blocks (providerProtected n o c initial)=true
  pendingApart : spansApart (Index.callStack initial 135 false) (providerPending c)=true

theorem providerCheck_sound {n o c initial ra config}
    (checked : providerCheck n o c initial ra config=.ok ()) : ProviderFacts n o c initial ra config := by
  unfold providerCheck at checked
  obtain ⟨u,wide,checked⟩ := bind_ok checked
  cases u
  obtain ⟨mode,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨capacity,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨u,privateCheck,checked⟩ := bind_ok checked
  cases u
  obtain ⟨privateApart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨pendingApart,_⟩ := check_ok _ _ _ _ checked
  have mode : initial.data.system.cpl=0 ∧ initial.data.system.bits[10]=false := by simpa using mode
  have capacity : ¬(Context.mk c.coverage (c.preempt+512)).Needed ∨ 0<c.coverage.capacity.toNat := by
    simpa using capacity
  exact ⟨Index.callFrameCheck_sound wide,mode.1,mode.2,
    fun needed => capacity.elim (fun no => False.elim (no needed)) id,
    privateCheck,privateApart,pendingApart⟩

theorem ProviderFacts.private_heap {n o c initial ra config}
    (facts : ProviderFacts n o c initial ra config) :
    ∀ a, RandomProvider.PrivateBytes config a → ¬Index.HeapBytes n o a :=
  spansApart_disjoint facts.privateApart (fun _ h => h)
    ((show Covers (Index.storageSpans n o) (Index.HeapBytes n o) from fun _ h => h).append_left.append_left.append_left)

theorem ProviderFacts.private_live {n o c initial ra config}
    (facts : ProviderFacts n o c initial ra config) :
    ∀ a, RandomProvider.PrivateBytes config a → ¬Index.LiveStack initial 135 a :=
  spansApart_disjoint facts.privateApart (fun _ h => h)
    (Index.live_cover initial 135).append_right.append_left.append_left

theorem ProviderFacts.private_services {n o c initial ra config}
    (facts : ProviderFacts n o c initial ra config) :
    ∀ a, RandomProvider.PrivateBytes config a →
      ¬(AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a) :=
  spansApart_disjoint facts.privateApart (fun _ h => h)
    (Trie.callServices_cover c).append_right.append_left

theorem ProviderFacts.private_external {n o c initial ra config}
    (facts : ProviderFacts n o c initial ra config) :
    ∀ a, RandomProvider.PrivateBytes config a → ¬Index.External c initial 7 a := by
  intro a privateByte external
  rcases external with stack | buffer | preempt
  · exact facts.private_live a privateByte
      (Stack.reserve_mono _ 7 135 8 (by decide) a (Index.stack_live stack))
  · exact facts.private_services a privateByte (.inl (.inr ⟨buffer.1,.inr buffer.2⟩))
  · exact facts.private_services a privateByte (.inr preempt)

theorem ProviderFacts.private_frame {n o c initial ra config before after}
    (facts : ProviderFacts n o c initial ra config)
    (frame : EqualOutside (fun a => Index.HeapBytes n o a ∨ Index.External c initial 7 a) before after) :
    ∀ a, RandomProvider.PrivateBytes config a → before.get? a=after.get? a := by
  intro a privateByte
  exact frame a (fun written => written.elim
    (facts.private_heap a privateByte) (facts.private_external a privateByte))

#print axioms providerCheck_sound
#print axioms ProviderFacts.private_frame
end Binary.Pair.Insert
