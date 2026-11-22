module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtFrRdA
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000

namespace GlobalTheory.FrameEquiv.GenMove

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {r g : ℕ}


end Classical

section Adelic

open GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

variable {D : D7}

theorem isUnitFr_of_archM (W : HSp D) (X : Data D.host.E W.rank) (hX : ModelW W rfl X)
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ} (h0 : IsOrthogonalFrame X x₀)
    {th : X.Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hth : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ))
    (g : GA D W) (x : Frame X.Ψ W.rank)
    (hx : ∀ τ : X.Ψ, mat x τ = Matrix.reindex (finCongr rfl) (finCongr rfl) (archM W (th τ) g) * x₀ τ.1) :
    IsUnitFr X x := by
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x
    fun τ => ?_).2
  rw [← h0 τ.1 τ.2, hx τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary W (hth τ) g
  have e1 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) W.gram).transpose).map τ.1).transpose =
      -(W.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end Adelic

end GlobalTheory.FrameEquiv.GenMove

