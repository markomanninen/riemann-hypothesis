module

public import Mathlib
public import Formalism.HermitianLattices.StatementMass
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiStatOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianRepresents

@[expose] public section

namespace GlobalTheory.Mass

theorem siegelMassRatio_holds : Formalism.HermitianLatticesTheory.SiegelMassRatio :=
  Formalism.HermitianLattices.Ext.L3.siegelMassRatio_of_LI binary_hermitian_represents Formalism.HermitianLattices.Ext.L3.liStat

end GlobalTheory.Mass
