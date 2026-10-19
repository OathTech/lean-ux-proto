import Leanux.Proofs.WG.TransmitSecurity.PacketAllocation
import Leanux.Proofs.Logged.NativeCapture

/-! The native batch allocator has no hidden allocation or clock choice. With
a resident device it completes the entire map; without one it stops on the first
read. This rules out an unrecorded allocated prefix between these source cuts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The actual mapM allocation is total from every resident device, independent
of initialized reachability and packet contents. -/
theorem total (packets : List DataPacket) (w : WGWorld) (a : Ambient) (d : Device)
    (device : w.dev = some d) :
    ∃ item v, ((packets.mapM newTxSkb).run w).run a = .ok ((item,v),a) ∧ v.dev.isSome = true := by
  induction packets generalizing w d with
  | nil => exact ⟨[],w,rfl,by simp [device]⟩
  | cons packet packets ih =>
    let u := Packets.update w fun v =>
      {v with txSkbs := v.txSkbs.insert d.nextSkb packet,nextSkb := d.nextSkb + 1}
    let next := {d with txSkbs := d.txSkbs.insert d.nextSkb packet,nextSkb := d.nextSkb + 1}
    have resident : u.dev = some next := by simp [u,next,Packets.update,device]
    obtain ⟨item,v,run,after⟩ := ih u next resident
    refine ⟨d.nextSkb :: item,v,?_,after⟩
    simp only [List.mapM_cons,StateT.run_bind,Packets.newTxSkb_run w a d packet device,
      CounterWindow.except_ok_bind]
    change (((packets.mapM newTxSkb).run u).run a >>= fun value => pure ((d.nextSkb :: value.1.1,value.1.2),value.2)) = _
    rw [run]
    rfl

/-- A failure is possible only before the first allocation: the input device
is absent and the requested list is nonempty. -/
theorem stopped_entry (packets : List DataPacket) (w : WGWorld) (a : Ambient) (stop : Stop)
    (run : ((packets.mapM newTxSkb).run w).run a = .error stop) :
    w.dev = none ∧ packets ≠ [] := by
  constructor
  · cases device : w.dev with
    | none => rfl
    | some d =>
      obtain ⟨item,v,normal,_⟩ := total packets w a d device
      rw [normal] at run
      cases run
  · intro empty
    subst packets
    cases run

/-- The only stopped map is exactly the first allocation's missing-device
read, before any store write or later packet is reached. -/
theorem stopped_first (packet : DataPacket) (packets : List DataPacket)
    (w : WGWorld) (a : Ambient) (stop : Stop)
    (run : (((packet :: packets).mapM newTxSkb).run w).run a = .error stop) :
    ((newTxSkb packet).run w).run a = .error stop := by
  have absent := (stopped_entry (packet :: packets) w a stop run).1
  simpa [List.mapM_cons,newTxSkb,Framing.liftSkb_run,absent,
    invariant,AmbientM.invariant] using run

/-- A completed native batch emits its allocation receipt before any create
or publication suffix can run or stop. -/
theorem observed_total (packets : List DataPacket) (w : WGWorld) (a : Ambient) (d : Device)
    (device : w.dev = some d) (h : List E) (record : WGRunWitness (List SkbId) → E) :
    ∃ item v, runWGPrefix (receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb)) record) w a h =
      (.ok ((item,v),a),h ++ [record ⟨item,w,v,a,a⟩]) ∧
      item = List.range' d.nextSkb packets.length ∧
      ∀ (n : Nat) packet, packets[n]? = some packet →
        ∃ id, item[n]? = some id ∧ Queues.TxDisposition.txPackets v id = some packet := by
  obtain ⟨item,v,run,_⟩ := total packets w a d device
  refine ⟨item,v,?_,(Queues.TxDisposition.ItemSeparation.allocate_result packets device run).1,
    TransmitSecurity.PacketAllocation.records packets device run⟩
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift,run]

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Allocation
