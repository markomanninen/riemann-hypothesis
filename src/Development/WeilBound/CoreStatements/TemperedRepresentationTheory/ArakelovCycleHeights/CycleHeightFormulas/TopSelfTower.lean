module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreeEqOrderSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Formalism.DegreeFormula.PointDegree.PowSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseOfFlagCpt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodChernWeilOfGoodTopChernForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArithmeticHeightTower.TowerCopy

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.VdmRec GlobalTheory.ProjVar

theorem topSelf_eq_finrank_mul {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (M : LB X) (d : ℕ) : topSelfIntersection k M d = (Module.finrank k K : ℤ) * topSelfIntersection K M d := by
  have hχ (F : X.Modules) : chi k F = (Module.finrank k K : ℤ) * chi K F := by
    have hT (n : ℕ) : IsScalarTower k K (coh F n) := by
      refine ⟨fun a b x => ?_⟩
      change cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) (a • b)) x =
        cohOn.action F ⊤ n (algebraMap k Γ(X, ⊤) a) (cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) b) x)
      rw [Algebra.smul_def, map_mul, map_mul, hk]
      rfl
    have e (n : ℕ) : ((-1 : ℤ) ^ n * hdim k F n) = (Module.finrank k K : ℤ) * ((-1 : ℤ) ^ n * hdim K F n) := by
      rw [hdim_def, hdim_def, ← Module.finrank_mul_finrank k K (coh F n)]
      push_cast
      ring
    rw [chi_def, chi_def]
    simp_rw [e]
    exact (mul_finsum _ _).symm
  rw [topSelf_def, topSelf_def, interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hχ]
  ring

end GlobalTheory.ArithmeticHeightTower.TowerCopy
