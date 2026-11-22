module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardPulledSectionsFormBasisEqPowDim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_pulledSectionsFormBasis_eq_pow_dim : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  first | exact @GlobalTheory.LN.SecRank.card_basis_eq_pow | exact GlobalTheory.LN.SecRank.card_basis_eq_pow | (intros; apply GlobalTheory.LN.SecRank.card_basis_eq_pow <;> assumption)
