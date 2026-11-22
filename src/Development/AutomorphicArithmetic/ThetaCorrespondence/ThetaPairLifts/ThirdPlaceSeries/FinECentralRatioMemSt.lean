module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterMtEqSmulOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntLocIffValBar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselAwayPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalComponentData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairScalar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFrames
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioStabLocAtLevelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioStabAtTStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioUnitGenStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem finE_centralRatio_mem_St_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hrS u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hz hzc k hk he
  have hm : 0 < D.R.m := by unfold Ranks.rS at hrS; omega
  have hfr := (_root_.GlobalTheory.Fam.sdY_frames_alt W hW 0 hm).2
  rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) (W.Q.Rl.βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hfr]
  intro v
  by_cases hg : ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · exact _root_.GlobalTheory.T.placed_bessel_pair_scalar_alt W hW hrS u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hz hzc k hk he v hg
  · push Not at hg
    by_cases ht : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
    · exact _root_.GlobalTheory.T.placed_bessel_pair_character_alt W hW hrS u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hz hzc k hk he v hg ht
    · push Not at ht
      exact _root_.GlobalTheory.T.placed_bessel_pair_translate_alt W hW hrS u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hz hzc k hk he v hg ht.1 ht.2
end GlobalTheory.MiTop
end
end
