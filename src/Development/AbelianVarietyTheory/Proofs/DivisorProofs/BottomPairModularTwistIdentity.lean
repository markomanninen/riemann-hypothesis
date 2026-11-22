module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfOfChars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Matrix

namespace GlobalTheory.BotRealInv

theorem substF_minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n)
    (H : D.what₂.Tau → Matrix (Fin a₁) (Fin a₁) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) (fun τ => (H τ)ᵀ) (GlobalTheory.BotFormula.minorF ha hd T) =
      (∏ τ, (H τ).det ^ n τ) • GlobalTheory.BotFormula.minorF ha hd T := by
  subst ha hd
  have e : GlobalTheory.BotFormula.minorF (rfl : a = a) (rfl : d = d) T = GlobalTheory.NormSum.minorPol D T := by
    unfold GlobalTheory.BotFormula.minorF
    exact MvPolynomial.rename_id_apply _
  rw [e]
  have one : ∀ (τ : D.what₂.Tau) (s : Fin a → Fin d),
      GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) (fun τ => (H τ)ᵀ)
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det =
      MvPolynomial.C (H τ).det *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_transpose ((MvPolynomial.C : ℂ →+* _).mapMatrix (H τ)), mul_comm,
      ← Matrix.det_mul]
    congr 1
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X,
      RingHom.mapMatrix_apply, Matrix.transpose_apply]
    rw [Finset.sum_eq_single (s i)]
    · simp only [Matrix.one_apply_eq, one_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [GlobalTheory.NormSum.minorPol, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  simp only [one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

theorem succ_mul_succ_sub_one_div_succ {G : Type*} [CommGroup G] (a e c : G) : a * e / (c * e) = a / c := mul_div_mul_right_eq_div _ _ _

end GlobalTheory.BotRealInv

end
