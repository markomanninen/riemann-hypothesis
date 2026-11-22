module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarProved
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensPf
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSplit
public import Formalism.PeriodIntegrals.VolFromSW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoPolish
public import Formalism.PeriodIntegrals.WeilQuotMeas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousHAIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MemSpanRIffSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousCrdAllSymm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactStabGLHat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.LatHat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AprimeInf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstFinal

@[expose] public section

namespace Formalism.L2.SG.Closed

theorem AprimeInf_holds [hG : Fact PI.AprimeInfW.GaugeVolUD] : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  PI.AprimeInfAsm.aprime_infinite_real Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds hG.out

variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem JacGauge_holds : Formalism.L2.SG.Pf.JacGauge := Formalism.L2.SG.Pf.jacGauge

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem RealBracket_holds (hC : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) : Formalism.L2.SG.Pf.NcReal.RealBracket :=
  Formalism.L2.SG.Pf.NcReal.JX.realBracket_of_jac JacGauge_holds hC AprimeInf_holds
    (fun n ε => Formalism.MainNotions.S.Gauge.gauge_density_exists n ε)

end Formalism.L2.SG.Closed
