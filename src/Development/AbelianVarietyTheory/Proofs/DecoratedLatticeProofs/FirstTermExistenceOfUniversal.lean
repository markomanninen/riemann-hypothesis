module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwartStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP

@[expose] public section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.FirstTermCompare

variable {D : D7}

theorem hasIw_of_good {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) := by
  have h := GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2) l hl
  exact ⟨h.1, h.2.1⟩

end GlobalTheory.RegSch.FirstTermCompare

end
