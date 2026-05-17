import TauLib.BookIII.Bridge.TauCircleParam
import TauLib.BookIII.Bridge.LemniscateGraph
import TauLib.BookIII.Bridge.LemniscateHilbert
import TauLib.BookIII.Bridge.LemniscateOperatorSpine
import TauLib.BookIII.Bridge.O3Status
import TauLib.BookIII.Bridge.FiniteSpectralDeterminant
import TauLib.BookIII.Bridge.O3Interface

/-!
# TauLib.BookIII.Bridge.LemniscateSpine

Aggregate import for the experimental G5 lemniscate graph/Hilbert/operator
spine and the paired explicit O3 interface.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

/-- Smoke-level marker that the G5 spine modules elaborate together. -/
def g5_lemniscate_spine_loaded : Bool := true

theorem g5_lemniscate_spine_loaded_check :
    g5_lemniscate_spine_loaded = true := rfl

end Tau.BookIII.Bridge
