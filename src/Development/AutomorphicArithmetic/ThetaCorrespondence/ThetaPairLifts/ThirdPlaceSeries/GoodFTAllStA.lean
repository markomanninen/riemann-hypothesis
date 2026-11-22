module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgreeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTypeVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InfinitesimalCharacterReference
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllOfLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameParamRecordLe
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
set_option maxHeartbeats 2000000 in
theorem goodFTAll_stA_alt (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep) (hlab : GlobalTheory.CoefDuty.OPinModel.LabFixed D)
    (hloc : ∀ (I : GlobalTheory.TypeRec.Ident D) cp, GlobalTheory.TypeRec.IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) : GoodFTAll D := by
  refine _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_of_local_alt hG hZ hL D a.A.wdT a.A.row rep
    (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) a.row a.depth hlab
    (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (D.host.g k) ⟨D.host.g_prime k⟩) ?_ hloc
  intro I rc hrc k v
  refine _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D a.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) k v (a.A.grp.kv k v) ?_
  rw [← a.zeta k]
  exact a.A.grp.tg_tame k v
end DiscreteGroups.sglob.DzType.Rt
end
