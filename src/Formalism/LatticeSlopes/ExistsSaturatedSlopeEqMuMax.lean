module

public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
public import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
public import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
public import Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated
public import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained
public import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin
public import Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum

@[expose] public section

namespace Formalism.F

theorem covolEqGram : CovolEqGram := covol_eq_gram
theorem covolPos : CovolPos := covol_pos'
theorem covolBasic : CovolBasic := covol_basic_properties
theorem covolEqCovolume : CovolEqCovolume := covol_eq_covolume'
theorem gramDetLe : GramDetLe := gram_det_le
theorem slopesBdd : SlopesBdd := slopesBdd_of gramDetLe
theorem slopeLeMuMax : SlopeLeMuMax := slopeLeMuMax_of slopesBdd
theorem degQuot : DegQuot := degree_quotient
theorem covolAntiSameRank : CovolAntiSameRank := covol_anti_same_rank
theorem saturProps : SaturProps := saturation_properties
theorem shortVector : ShortVector := shortVector_of covolEqCovolume
theorem finiteSaturated : FiniteSaturated := finiteSaturated_of shortVector
theorem muMaxLeMin : MuMaxLeMin := muMaxLeMin_of covolPos shortVector
theorem orthSum : OrthSum := orthogonal_sum_slope

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem covol_pos (L : Submodule ℤ E) [DiscreteTopology L] : 0 < covol L :=
  covolPos E L ‹_›

theorem deg_eq_deg_add_deg_quot {L N : Submodule ℤ E} [DiscreteTopology L] (hN : IsSaturated L N) :
    deg L = deg N + deg (quot L N) :=
  (degQuot E L N ‹_› hN).2.2

end

end Formalism.F
