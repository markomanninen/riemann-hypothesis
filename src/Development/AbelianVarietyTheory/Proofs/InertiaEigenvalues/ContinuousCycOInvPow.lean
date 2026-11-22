module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

@[expose] public section

noncomputable section

namespace GlobalTheory.AdmLoc.CycWitness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct

section Line

variable {G Qp LL R : Type} [Group G] [Field Qp] [Field LL] [Algebra Qp LL] [CommRing R] [Algebra Qp R]

end Line

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

variable (hK : Function.Surjective (algebraMap Qp K)) (a : ℕ) (θ : G →* LLˣ)
  (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (((PD.χ g)⁻¹ ^ a : Qpˣ) : Qp))


include hK hθ

end Per

variable {l : ℕ} [Fact l.Prime]

def cycO (P : LocPrime l) (K LL : FinExt l) : ↥(GK K) →* (↥(OL LL))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem P K LL g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }

theorem cycO_val (P : LocPrime l) (K LL : FinExt l) (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (cycO P K LL g) = algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g) := rfl

end GlobalTheory.AdmLoc.CycWitness
