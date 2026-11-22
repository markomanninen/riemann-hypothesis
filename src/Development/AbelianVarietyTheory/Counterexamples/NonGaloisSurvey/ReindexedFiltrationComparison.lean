module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq

@[expose] public section

noncomputable section

namespace GlobalTheory.Survey.SlowDecayFunctions

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

section Datum

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

end Datum

variable {l : ℕ} [Fact l.Prime]

theorem continuous_cyc (P : LocPrime l) (K LL : FinExt l) :
    Continuous fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) := by
  have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
  have e : (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) =
      fun g : ↥(GK K) => algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    funext g
    change algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
    rw [P.PD_χ]
  rw [e]
  refine Continuous.subtype_mk (f := fun g : ↥(GK K) =>
    algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])) ?_ _
  exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h.comp continuous_subtype_val)

section Triv

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    (LL : Type) [Field LL] [Algebra Qp LL]

end Triv

end GlobalTheory.Survey.SlowDecayFunctions
