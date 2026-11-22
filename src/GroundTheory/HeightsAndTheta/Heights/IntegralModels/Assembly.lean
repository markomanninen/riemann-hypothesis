module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueSat
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ComapEqMaximalIdeal
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IicEqRange
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.CpEqPrimeWeight

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem BlowUpChart.full : BlowUpChart.Statement := BlowUpChart.proof

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement := FiniteIntegralClosure.proof

theorem MertensUpper.full : MertensUpper.Statement := MertensUpper.proof

theorem TorsionFreeQuotientLength.full : TorsionFreeQuotientLength.Statement := TorsionFreeQuotientLength.proof

theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

theorem FiniteNormalization.full : FiniteNormalization.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.normalization_of_scheme
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.scheme_of_alg
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.alg_iff.mp FiniteIntegralClosure.full))

end GroundTheory.Heights₂.Heights.Model

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem BlowUpChart.full : BlowUpChart.Statement :=
  BlowUpChart.equiv.mp GroundTheory.Heights₂.Heights.Model.BlowUpChart.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.equiv.mp GroundTheory.Heights₂.Heights.Model.KrullAkizuki.full

theorem MertensUpper.full : MertensUpper.Statement :=
  MertensUpper.equiv.mp GroundTheory.Heights₂.Heights.Model.MertensUpper.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.equiv.mp GroundTheory.Heights₂.Heights.Model.SumCp.full

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement :=
  FiniteIntegralClosure.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full,
    GroundTheory.Heights₂.Heights.Model.FiniteNormalization.full⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
