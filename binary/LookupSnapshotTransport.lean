import LookupFrameTransport
import LookupSourceFrame
import KeypairRepresentation

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

abbrev ReceivingSnapshot := Nat × (KeypairId → Option (Nat × ReplayCounter))

/-- Exact bytes for the frontier and every source-live keypair's lifetime
    stamp and full replay window. This does not assert an allocation bitmap
    for absent IDs: slot existence is preserved by the source frame theorem,
    and a physical allocator interpretation is outside lookup's read set. -/
def ReceivingSnapshotFields (addresses : KeypairId → Address) (memory : Mem 64)
    (snapshot : ReceivingSnapshot) : Prop :=
  Layouts.KeypairCounterField memory snapshot.1 ∧
  ∀ id stamp counter, snapshot.2 id = some (stamp, counter) →
    memory.loadInt (addresses id + .ofNat 64 Layouts.keypair_internal_id) 8 = some (stamp : Int) ∧
    Layouts.ReplayFields memory (addresses id + .ofNat 64 Layouts.keypair_receiving_counter) counter

def ReceivingSnapshotReads (addresses : KeypairId → Address) (snapshot : ReceivingSnapshot)
    (address : Address) : Prop :=
  InRange Layouts.keypairCounterAddress 8 address ∨
  ∃ id value, snapshot.2 id = some value ∧ Layouts.KeypairSnapshotFootprint (addresses id) address

theorem ReceivingSnapshotFields.frame {addresses : KeypairId → Address}
    {snapshot : ReceivingSnapshot} {before after : Mem 64} {writes : Address → Prop}
    (same : EqualOutside writes before after)
    (separate : ∀ a, ReceivingSnapshotReads addresses snapshot a → ¬writes a)
    (represented : ReceivingSnapshotFields addresses before snapshot) :
    ReceivingSnapshotFields addresses after snapshot := by
  refine ⟨Layouts.KeypairCounterField.frame same snapshot.1
    (fun i hi => separate _ (.inl ⟨i, hi, rfl⟩)) represented.1, ?_⟩
  intro id stamp counter present
  have fields := represented.2 id stamp counter present
  constructor
  · exact (same.loadInt _ 8 (fun i hi => separate _ (.inr ⟨id, (stamp,counter), present, .inl ⟨i,hi,rfl⟩⟩))).symm.trans fields.1
  · apply Layouts.ReplayFields.frame same _ _ _ fields.2
    intro i hi
    exact separate _ (.inr ⟨id, (stamp,counter), present, .inr ⟨i,hi,rfl⟩⟩)

/-- Concrete frame instance for the lifetime/replay observations, alongside
    arbitrary P on the same accepted run. The untouched-byte separation is
    a frame-rule premise, not a restriction added to Pre_lookup. -/
theorem lookup_snapshot_transport (fetch : Int64 → Option Decoded)
    (decoder : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp4 : TraceCmp4Contract fetch)
    (traceConstCmp4 : TraceConstCmp4Contract fetch) (traceConstCmp1 : TraceConstCmp1Contract fetch)
    (bhEnable : BhEnableContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (initial : MachineState) (world : World)
    (onlineCPUs : Nat) (externalActions : List Nat) (permissions : Permissions)
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : InvocationPermissions fetch permissions initial (Image.Lookup.entry+0x94))
    (pre : Pre_lookup c coverage preempt returnAddress initial world)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld))
    (P : MirrorHistory.Run (Option (IndexOwner × PeerId)) → Prop)
    (property : ∀ run, MirrorHistory.Accepted (MirrorHistory.lookup c.kinds c.query) world run → P run)
    (represented : ReceivingSnapshotFields c.keypairs initial.data.dmem (LookupSourceFrame.receivingSnapshot world))
    (separate : ∀ v, LookupEntry c coverage preempt returnAddress initial world v →
      ∀ a, ReceivingSnapshotReads c.keypairs (LookupSourceFrame.receivingSnapshot world) a →
        ¬LookupWrites c coverage preempt initial.data v a) :
    Eventually (historyStep fetch) (fun final =>
      LookupPost c coverage preempt returnAddress initial world answer finalWorld final ∧
      RunEnvironment fetch permissions onlineCPUs externalActions final.history ∧
      ∃ run, run.result = answer ∧ run.finalWorld = finalWorld ∧
        MirrorHistory.Accepted (MirrorHistory.lookup c.kinds c.query) world run ∧
        FramedLookupRun c LookupSourceFrame.receivingSnapshot (ReceivingSnapshotFields c.keypairs) final run ∧ P run)
      ⟨initial, [initial]⟩ := by
  exact lookup_framed_transport fetch decoder tracePc traceCmp4 traceConstCmp4 traceConstCmp1 bhEnable
    c coverage preempt returnAddress initial world onlineCPUs externalActions permissions environment access pre answer finalWorld accepted P property
    LookupSourceFrame.receivingSnapshot (ReceivingSnapshotFields c.keypairs) represented
    (fun v entry _ _ same fields => fields.frame same (separate v entry))
    (fun run acceptedRun => LookupSourceFrame.lookup_receivingSnapshot c.kinds c.query world
      run.finalWorld run.result run.points acceptedRun)

#print axioms ReceivingSnapshotFields.frame
#print axioms lookup_snapshot_transport
end Binary.LookupRelation
