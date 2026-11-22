module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RowsCongrOfTrivialAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionFixesLevelVectorUpToUnit

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.KernelCompare

variable {D : D7} {S T : HSp D}

theorem isTh_uVec (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) {f : WO S T → ℂ} (hf : C.IsTh f) :
    C.IsTh (C.uVec Lv hn f) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.ThetaSpace.theta_space_laws D S T C
  exact finsum_induction C.IsTh h0 (fun x y hx hy => (h1 x y hx hy).1)
    fun c => (h2 _ ((h2 f hf).2.1 _)).1 _

end GlobalTheory.Ker.KernelCompare
