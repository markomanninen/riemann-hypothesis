module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeVectorOfGoodLevelRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalIsometriesInnerAutAdelicFrameIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesOddRankGap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalMultiplicityEqDiscreteSeriesModelMapsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermitiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.MultEqTrace

def conjEquiv {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (Φ Φ₀ : G ≃* H) (b : G) (hb : ∀ g, Φ g = Φ₀ (b * g * b⁻¹)) :
    Representation.Equiv (σ.comp Φ.symm.toMonoidHom : Representation ℂ H W)
      (σ.comp Φ₀.symm.toMonoidHom : Representation ℂ H W) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (σ b) (σ b⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun h => by
      have e : Φ.symm h = b⁻¹ * Φ₀.symm h * b := by
        apply Φ.injective
        rw [Φ.apply_symm_apply, hb]
        simp [mul_assoc]
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, e]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group

end GlobalTheory.MultEqTrace
