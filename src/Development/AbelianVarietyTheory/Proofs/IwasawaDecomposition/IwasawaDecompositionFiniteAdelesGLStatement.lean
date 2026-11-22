module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL : PIW.ClassFinD.IwasawaAf := by
  first | exact @GlobalTheory.IwasawaFinAd.iwasawaAf | exact GlobalTheory.IwasawaFinAd.iwasawaAf | (intros; apply GlobalTheory.IwasawaFinAd.iwasawaAf <;> assumption)
