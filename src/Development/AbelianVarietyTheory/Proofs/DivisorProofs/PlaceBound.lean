module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultSharpOfPlaceBound
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNumBlockSetsMulGammaTwoSidedBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityParabolicInductStatement

@[expose] public section

namespace GlobalTheory.FinGL.MultSharpObj

open GlobalTheory.FinGL Formalism.L2.DIV

theorem placeBound : MultSharpPf.PlaceBound := by
  intro F _ _ ψ hψ r V _ _ _ b σ hσ ρ k hk hr hq
  rw [GlobalTheory.T.symmetricPositionCharMultiplicity_parabolicInduction F ψ hψ r V b σ hσ ρ k hr]
  exact sum_numBlockSets_mul_gamma_two_sided_bounds r k (Fintype.card F) b hk (by omega) hq Fintype.one_lt_card

theorem multSharp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.MultSharp := MultSharpPf.multSharp_of_placeBound placeBound

end GlobalTheory.FinGL.MultSharpObj
