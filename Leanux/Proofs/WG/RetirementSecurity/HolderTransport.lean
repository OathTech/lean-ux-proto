import Leanux.Proofs.WG.RetirementSecurity.Holders

/-! Transport of the concrete holder projection. The carrier projection names
the actual peer slots and queues and actual packet cells. A transport must
preserve every allocation named by the old durable holders; final release may
still delete an allocation not named by any of those holders. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

def carrierShape (w : WGWorld) :=
  (peersAt w, (fun id : SkbId => w.dev.bind fun d => d.txSkbs[id]?),
    (fun id : SkbId => w.dev.bind fun d => d.rxSkbs[id]?))

theorem mapM_transport (f g : α → Option β) (xs : List α) (ys : List β)
    (run : xs.mapM f = some ys)
    (step : ∀ x y, y ∈ ys → f x = some y → g x = some y) :
    xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil => simpa using run
  | cons x xs ih =>
    cases first : f x with
    | none => simp [List.mapM_cons,first] at run
    | some y =>
      cases rest : xs.mapM f with
      | none => simp [List.mapM_cons,first,rest] at run
      | some tail =>
        simp [List.mapM_cons,first,rest] at run
        subst ys
        have head := step x y (by simp) first
        have tailRun := ih tail rest (fun z r member => step z r (by simp [member]))
        simp [List.mapM_cons,head,tailRun]

theorem nameLoan_transport (before : nameLoan w holder key = some loan)
    (resident : ∃ k, keyAt v loan.allocation.slot = some k ∧
      k.internalId = loan.allocation.stamp) :
    nameLoan v holder key = some loan := by
  obtain ⟨sameHolder,sameSlot,old,_,sameStamp⟩ := nameLoan_resident before
  obtain ⟨k,found,stamp⟩ := resident
  cases loan with
  | mk named allocation =>
    cases allocation with
    | mk slot generation =>
      simp only at sameHolder sameSlot sameStamp found stamp
      subst named
      subst slot
      simp [nameLoan,found,stamp]

def transmitLoan (w : WGWorld) (pid : PeerId) (batch : List SkbId) : Option KeyLoan := do
  let head ← batch.head?
  let packet ← w.dev.bind fun d => d.txSkbs[head]?
  nameLoan w (.transmit pid batch) packet.keypair

def receiveLoan (w : WGWorld) (pid : PeerId) (id : SkbId) : Option KeyLoan := do
  let packet ← w.dev.bind fun d => d.rxSkbs[id]?
  nameLoan w (.receive pid id) packet.keypair

theorem peerLoans_eq (w : WGWorld) (pid : PeerId) (p : Peer) :
    peerLoans w pid p = (do
      let next ← p.keypairNext.toList.mapM (nameLoan w (.peerSlot pid .next))
      let previous ← p.keypairPrevious.toList.mapM (nameLoan w (.peerSlot pid .previous))
      let current ← p.keypairCurrent.toList.mapM (nameLoan w (.peerSlot pid .current))
      let tx ← p.txQueue.all.mapM (transmitLoan w pid)
      let rx ← p.rxQueue.all.mapM (receiveLoan w pid)
      return next ++ previous ++ current ++ tx ++ rx) := rfl

theorem peerLoans_transport (pid : PeerId) (p : Peer) (loans : List KeyLoan)
    (shape : carrierShape v = carrierShape w)
    (before : peerLoans w pid p = some loans)
    (resident : ∀ loan ∈ loans, ∃ k,
      keyAt v loan.allocation.slot = some k ∧ k.internalId = loan.allocation.stamp) :
    peerLoans v pid p = some loans := by
  have txShape := congrArg (fun shape => shape.2.1) shape
  have rxShape := congrArg (fun shape => shape.2.2) shape
  cases hn : p.keypairNext.toList.mapM (nameLoan w (.peerSlot pid .next)) with
  | none => simp [peerLoans_eq,hn] at before
  | some next =>
    cases hp : p.keypairPrevious.toList.mapM (nameLoan w (.peerSlot pid .previous)) with
    | none => simp [peerLoans_eq,hn,hp] at before
    | some previous =>
      cases hc : p.keypairCurrent.toList.mapM (nameLoan w (.peerSlot pid .current)) with
      | none => simp [peerLoans_eq,hn,hp,hc] at before
      | some current =>
        cases ht : p.txQueue.all.mapM (transmitLoan w pid) with
        | none => simp [peerLoans_eq,hn,hp,hc,ht] at before
        | some tx =>
          cases hr : p.rxQueue.all.mapM (receiveLoan w pid) with
          | none => simp [peerLoans_eq,hn,hp,hc,ht,hr] at before
          | some rx =>
            simp [peerLoans_eq,hn,hp,hc,ht,hr] at before
            subst loans
            have nextRun := mapM_transport _ (nameLoan v (.peerSlot pid .next)) _ _ hn
              (fun _ loan member found => nameLoan_transport found
                (resident loan (by simp [member])))
            have previousRun := mapM_transport _ (nameLoan v (.peerSlot pid .previous)) _ _ hp
              (fun _ loan member found => nameLoan_transport found
                (resident loan (by simp [member])))
            have currentRun := mapM_transport _ (nameLoan v (.peerSlot pid .current)) _ _ hc
              (fun _ loan member found => nameLoan_transport found
                (resident loan (by simp [member])))
            have txRun := mapM_transport _ (transmitLoan v pid) _ _ ht (by
              intro batch loan member found
              unfold transmitLoan at found ⊢
              cases head : batch.head? with
              | none => simp [head] at found
              | some id =>
                cases packet : w.dev.bind (fun d => d.txSkbs[id]?) with
                | none => simp [head,packet] at found
                | some pkt =>
                  have newPacket := congrFun txShape id
                  simp only [carrierShape] at newPacket
                  rw [packet] at newPacket
                  have named : nameLoan w (.transmit pid batch) pkt.keypair = some loan := by
                    simpa [head,packet] using found
                  have moved := nameLoan_transport named (resident loan (by simp [member]))
                  simpa [head,newPacket] using moved)
            have rxRun := mapM_transport _ (receiveLoan v pid) _ _ hr (by
              intro id loan member found
              unfold receiveLoan at found ⊢
              cases packet : w.dev.bind (fun d => d.rxSkbs[id]?) with
              | none => simp [packet] at found
              | some pkt =>
                have newPacket := congrFun rxShape id
                simp only [carrierShape] at newPacket
                rw [packet] at newPacket
                have named : nameLoan w (.receive pid id) pkt.keypair = some loan := by
                  simpa [packet] using found
                have moved := nameLoan_transport named (resident loan (by simp [member]))
                simpa [newPacket] using moved)
            simp [peerLoans_eq,nextRun,previousRun,currentRun,txRun,rxRun]

theorem durableLoans_transport (loans : List KeyLoan)
    (shape : carrierShape v = carrierShape w)
    (before : durableLoans w = some loans)
    (resident : ∀ loan ∈ loans, ∃ k,
      keyAt v loan.allocation.slot = some k ∧ k.internalId = loan.allocation.stamp) :
    durableLoans v = some loans := by
  have peers := congrArg (fun shape => shape.1) shape
  change peersAt v = peersAt w at peers
  cases oldDevice : w.dev with
  | none =>
    simp [durableLoans,oldDevice] at before
    subst loans
    cases newDevice : v.dev with
    | none => simp [durableLoans,newDevice]
    | some d => simp [peersAt,oldDevice,newDevice] at peers
  | some d =>
    cases newDevice : v.dev with
    | none => simp [peersAt,oldDevice,newDevice] at peers
    | some e =>
      have samePeers : e.peers = d.peers := by simpa [peersAt,oldDevice,newDevice] using peers
      cases mapped : d.peers.toList.mapM (fun (pid,p) => peerLoans w pid p) with
      | none => simp [durableLoans,oldDevice,mapped] at before
      | some groups =>
        simp [durableLoans,oldDevice,mapped] at before
        subst loans
        have newMapped := mapM_transport _ (fun (pid,p) => peerLoans v pid p) _ _ mapped (by
          intro pair group member found
          apply peerLoans_transport pair.1 pair.2 group shape found
          intro loan inside
          exact resident loan (List.mem_flatten.mpr ⟨group,member,inside⟩))
        simp [durableLoans,newDevice,samePeers,newMapped]

end Leanux.Proofs.WG.RetirementSecurity
