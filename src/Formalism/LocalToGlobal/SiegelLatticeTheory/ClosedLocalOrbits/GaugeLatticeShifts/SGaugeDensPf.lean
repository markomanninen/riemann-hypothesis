module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensJ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensV

@[expose] public section

namespace Formalism.MainNotions.S.Gauge

theorem gauge_density_exists : ∀ (n : ℕ) (ε : Fin n → Bool), GaugeDens ε := fun _ ε =>
  gaugeDens_of_parts ε (chartNhd ε) (transC ε) (jacInv ε) (locInvOf ε) (ballFormOf ε) (densOfBall ε)

end Formalism.MainNotions.S.Gauge
