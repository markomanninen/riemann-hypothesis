module

public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositiveStatement

@[expose] public section

namespace GlobalTheory

theorem hermRepUnram : Formalism.HermitianLattices.Ext.L3.HermRepUnram := GlobalTheory.T.binaryHermitianForm_represents_totallyPositive

instance : Fact (Formalism.HermitianLattices.Ext.L3.HermRepUnram) := ⟨hermRepUnram⟩

end GlobalTheory
