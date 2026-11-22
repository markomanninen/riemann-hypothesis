module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowest
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
namespace GlobalTheory.LiftSplitLoc
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
theorem locG_rankOne_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) (cs : CharSide D cf) (π : D.naut.CG 1) (w : PlE D.host)
    (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (cs.e1 π).1 w ξ) :
    T.e w (D.naut.locG π w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  have := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (cg.e 1 π)).1 with hχ'
  set χ := (cs.e1 π).1 with hχ
  have hloc (v : PlE D.host) : T.e v (D.naut.locG π v) =
      ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v) := by
    rw [hχ', CGu.ofChar_equivChar]
    exact cg.loc 1 π v
  have unr' (v : PlE D.host) : D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := by
    rw [T.unr v (D.naut.locG π v), hloc v]
    exact _root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' (D.nd.plOm.2 v)
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (cs.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · change χ'.loc v x * (χ.loc v x)⁻¹ = 1
      rw [u2 x hx, u1 x hx, inv_one, mul_one]
    · have hf := cs.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact _root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨ParLaws.isSmoothChar_loc χ w, fun _ => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep]
  rw [hchar]
  rfl
end GlobalTheory.LiftSplitLoc
namespace GlobalTheory.LiftSplitLoc
end GlobalTheory.LiftSplitLoc
end
end
