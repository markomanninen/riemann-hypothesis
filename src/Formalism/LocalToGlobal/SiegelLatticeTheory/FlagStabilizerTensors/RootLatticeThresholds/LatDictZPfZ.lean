module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ZOrbitOfOpen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPlane
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlue

@[expose] public section

namespace Formalism.L2.SG.Pf.LatDictZ

theorem anisotropic_vector_orbit : LatDictZ.ZOrbit :=
  zOrbit_of_open Z2.primitive_plane_local Z5.adelic_gluing

end Formalism.L2.SG.Pf.LatDictZ
