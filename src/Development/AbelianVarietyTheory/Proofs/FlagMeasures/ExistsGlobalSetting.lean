module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.PeriodIntegrals.BesselMapUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.SettingExistsOfGap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JExistsAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatExistsOfForms0
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MExistsHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFunctionBlockExistsOfBesselCoef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMatchHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcExistsAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelConjHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RescaleStep3
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColDictCoreHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FullExistsOfLocTied
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinXOfDecay

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict

namespace GlobalTheory.St.SpectralData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transport {D : D7} (F : ∀ u, Formalism.L2.Forms.Forms0 D u)
    (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (hι : ∃ ιA, GlobalTheory.St.IsAdeleIso X ιA) (u : D.what₂.Word) :
    ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  obtain ⟨wt, hw⟩ := GlobalTheory.St.WittT.wittExists D X u
  obtain ⟨ιA, hι⟩ := hι
  obtain ⟨g0, hg0⟩ := GlobalTheory.St.G.genusMatch_holds D F X u wt ιA hw hι
  obtain ⟨h0, hL, hKm⟩ := GlobalTheory.St.G.levelConj_holds D F X hK u wt ιA g0 hw hι hg0
  choose hcf hcr using GlobalTheory.St.G.hcExists_all D F X u wt ιA h0 hw hι
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := GlobalTheory.jExists_all D F X u wt hw
  exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hKm⟩


open Formalism.L2.SG.SplitPrimeNormLemmas in
theorem exists_setting (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent)
    (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
      ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧
        (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
        ∀ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  have hB : BesselNVGap := Formalism.L2.SG.Closed.BesselNVGap_holds
  have hC : CoefWeightedLoc := Formalism.L2.SG.Closed.CoefWeightedLoc_holds
  let A := Formalism.L2.SG.InstExistsPf.instanceOfRecord D
  obtain ⟨L⟩ := GlobalTheory.St.Lat.latExists_of_forms0 D (F D.u₀)
  obtain ⟨P⟩ := Formalism.L2.SG.Closed.PsiExists_holds D A
  obtain ⟨Rf⟩ := Formalism.L2.SG.Closed.RefExists_holds D A L
  obtain ⟨Xu⟩ := Formalism.L2.SG.Closed.XuExists_holds D A L Rf
  obtain ⟨Bu⟩ := Formalism.L2.SG.Closed.BunExists_holds D hC hG A L P Rf
  obtain ⟨Pi⟩ := Formalism.L2.SG.Closed.PiExists_holds D A L
  obtain ⟨Mu⟩ := Formalism.L2.SG.Closed.MuExists_holds D A L
  obtain ⟨Wb⟩ := GlobalTheory.WBlockExists.realPlaceFunctionBlockExists_of_bessel_coef hB hC D hG A L P Rf Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := GlobalTheory.St.mExists_holds D A L P Rf Xu Bu Pi Mu Wb
  obtain ⟨mg, hg, mw, hw, hM', ψ, hψ, hstd, hCm, hL⟩ :=
    GlobalTheory.St.Rescale.rescaleStep3 hSW D (mk A L P Rf Xu Bu Pi Mu Wb Mb) hb hM
  refine ⟨Formalism.L2.SG.SettingExistsMeasured.withMeas (mk A L P Rf Xu Bu Pi Mu Wb Mb) mg hg mw hw, hb, ψ, rfl,
    fun _ => HEq.rfl, hM', hψ, hstd, hCm, hL, fun hK u => ?_⟩
  exact exists_transport F _ hK ⟨RingEquiv.refl _, fun _ => rfl, fun _ => Iff.rfl⟩ u

end GlobalTheory.St.SpectralData
