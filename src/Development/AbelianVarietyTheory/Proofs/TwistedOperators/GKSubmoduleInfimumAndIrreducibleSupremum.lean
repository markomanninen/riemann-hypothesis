module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibilityStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimCompactStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalProjectionPosDefSesquilinearFiniStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeSpanProjectionPreservesFiniteDimInvariantSubStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InMaxCompactOfModelFrameInvStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOfMemGKModuleGeneratedByStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepRightTranslationMaxCompactStaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeAdjointOfSkewFormStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandInvariantsSymmetricOfDerivativeAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsJointEigenDecompositionCommutingSymmetricOStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGKSubmoduleISupGelfandJointEigenspacesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandInvariantMemIntertwinedTypeSpanStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemISupJointEigenspacesInfOfStableSubmoduleStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem isGKSub_sInf (s : Set (Submodule ℂ (GA D V → ℂ))) (h : ∀ A ∈ s, IsGKSub θ M A) : IsGKSub θ M (sInf s) := by
  constructor
  · intro τ g hg f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  · intro τ X hX f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).lie τ X hX f (Submodule.mem_sInf.1 hf A hA)


open scoped Matrix in
variable {M} in
theorem InK.inv {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (h : InK M τ g) : InK M τ g⁻¹ := by
  obtain ⟨hU, hk⟩ := h
  have hfd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set k := M.fr τ * g * (M.fr τ)⁻¹ with hkdef
  have hku : k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := hk.1
  have hsk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
  have hks : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hku
  have hkdet : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨k, star k, hks, hsk⟩, rfl⟩
  have hdet : k.det = g.det := by
    rw [hkdef, Matrix.det_mul, Matrix.det_mul, mul_comm (M.fr τ).det, mul_assoc, ← Matrix.det_mul,
      Matrix.mul_nonsing_inv _ hfd, Matrix.det_one, mul_one]
  have hgd : IsUnit g.det := hdet ▸ hkdet
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
  refine ⟨?_, ?_⟩
  · show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hg1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ = k⁻¹ := by
      rw [hkdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hfd]
      simp only [Matrix.mul_assoc]
    have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hsk
    rw [e1, hinv]
    refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact hsk), ?_⟩
    have hJ : star (Formalism.REAL.Jm (M.ε τ)) = Formalism.REAL.Jm (M.ε τ) := Formalism.REAL.Jm_conjTranspose _
    have hcomm : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ, m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * m →
        star m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * star m := fun m hm => by
      have h2 : star (m * Formalism.REAL.Jm (M.ε τ)) = star (Formalism.REAL.Jm (M.ε τ) * m) := congrArg star hm
      rw [star_mul, star_mul, hJ] at h2
      exact h2.symm
    exact hcomm k hk.2

end GlobalTheory.CuspGK

end
