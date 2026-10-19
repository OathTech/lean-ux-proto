import CallbackAgreement
import CallbackPc

namespace Binary.Callback
open TrustBase

theorem bh_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    BhEnableContract fetch := service_agreement agree bh_image_contract

theorem pc_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    TracePcContract fetch := service_agreement agree pc_image_contract

#print axioms bh_contract
#print axioms pc_contract
end Binary.Callback
