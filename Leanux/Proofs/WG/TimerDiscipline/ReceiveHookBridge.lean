import Leanux.Proofs.WG.TimerDiscipline.ReceiveHookSource
/-! Native source linkage for a projected receive-hook inspection, tied to one actual caller execution and its full outcome. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.ReceiveHookJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Queues
open HookJournal
def observation (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (g : WGWorld) (ambient : Ambient) : Inspection :=
  let reached := runWGPrefix (consume pid pkt ep) g ambient []
  ⟨Campaign2.observeResult reached.1,reached.2⟩

def Inspection.Valid (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (before : Campaign2.Snapshot) (result : Inspection) : Prop :=
  ∃ g ambient, before = Campaign2.snapshot g ambient ∧
    result = observation pid pkt ep g ambient

def Inspection.Facts (pid : PeerId) (result : Inspection) : Prop :=
  ValidHistory result.receipts ∧ Scoped pid result.receipts

theorem observation_valid (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (g : WGWorld) (ambient : Ambient) :
    (observation pid pkt ep g ambient).Valid pid pkt ep (Campaign2.snapshot g ambient) :=
  ⟨g,ambient,rfl,rfl⟩

theorem observation_erases (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (g : WGWorld) (ambient : Ambient) :
    (observation pid pkt ep g ambient).outcome =
      Campaign2.observeResult (((consumeDataDone pid pkt ep).run g).run ambient) := by
  exact congrArg Campaign2.observeResult (consume_erases pid pkt ep g ambient [])

theorem observation_facts (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (g : WGWorld) (ambient : Ambient) :
    (observation pid pkt ep g ambient).Facts pid := by
  have valid := (consume_valid pid pkt ep g ambient [] (fun _ h=>by cases h)).choose_spec.2.1
  have scopeFact := (consume_scoped pid pkt ep g ambient [] (fun _ h=>by cases h)).choose_spec.2.1
  exact ⟨valid,scopeFact⟩

end Leanux.Proofs.WG.TimerDiscipline.ReceiveHookJournal
