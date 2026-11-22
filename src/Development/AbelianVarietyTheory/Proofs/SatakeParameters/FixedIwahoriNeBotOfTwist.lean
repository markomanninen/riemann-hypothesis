module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.IwaFix

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem fixed_iwahori_ne_bot_of_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (s : ℂ)
    (T : (twist ρ (detChar (Fin n) (absPow k s))).Equiv ρ') (h : fixed ρ' (iwahori k (Fin n)) ≠ ⊥) :
    fixed ρ (iwahori k (Fin n)) ≠ ⊥ := by
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
  refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun hx => h0 (by simp [hx])⟩
  have e := T.toIntertwiningMap.isIntertwining _ _ g x
  have hd : absPow k s (Matrix.GeneralLinearGroup.det g) = 1 := by
    have h1 := GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (iwahori_le_KO k (Fin n) hg)
    ext; simp [absPow, h1]
  rw [twist_apply, detChar_apply, hd, Units.val_one, one_smul] at e
  have hy' := GlobalTheory.Parabolic.mem_fixed.1 hy g hg
  exact T.toLinearEquiv.injective (e.trans hy')

end GlobalTheory.AboveL.IwaFix
