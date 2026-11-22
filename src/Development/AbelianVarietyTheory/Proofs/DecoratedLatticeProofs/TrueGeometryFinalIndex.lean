module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.RedAt

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
include hq

theorem val_lt_of_pr {y : D.host.E} (hy : valuation K (q.pr (incA D y)) < 1) : PP.valuation D.host.E y < 1 := by
  have val_lt_one_iff (x : 𝓞 D.host.E) :
      valuation K (q.pr (incA D (x : D.host.E))) < 1 ↔ x ∈ PP.asIdeal := by
    by_cases hx : x = 0
    · subst hx; simp
    have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
    rw [hq.2 x hx, ← q.sec_pr, ← q.int_iff]
    change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]
  have val_le_one (x : 𝓞 D.host.E) : valuation K (q.pr (incA D (x : D.host.E))) ≤ 1 := by
    have h := GlobalTheory.FinPl.SplitApprox.val_le q 1 one_pos (incA D (x : D.host.E)) (finPart D (incA D (x : D.host.E)))
      (GlobalTheory.FinPl.SplitApprox.tmul_mem (a := 1) (fun v => by rw [map_one]; exact one_mem _) x.2) (by simp)
    simpa using h
  by_cases hle : PP.valuation D.host.E y ≤ 1
  · obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hle
    have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
      le_antisymm (val_le_one _) (not_lt.1 fun h' => d.2 ((val_lt_one_iff _).1 h'))
    have hr : r ∈ PP.asIdeal := by
      refine (val_lt_one_iff r).1 ?_
      rw [show ((r : 𝓞 D.host.E) : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd,
        mul_one]
      exact hy
    have hdv : PP.valuation D.host.E ((d : 𝓞 D.host.E) : D.host.E) = 1 :=
      le_antisymm (PP.valuation_le_one _) (not_lt.1 fun h' => d.2 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 h'))
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).2 hr
    rw [← e, map_mul] at h1
    rwa [show algebraMap (𝓞 D.host.E) D.host.E (d : 𝓞 D.host.E) = ((d : 𝓞 D.host.E) : D.host.E) from rfl, hdv, mul_one] at h1
  · exfalso
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hle (by simp)
    have h1 : PP.valuation D.host.E y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ (not_le.1 hle)
    have h2 := GlobalTheory.SeeSaw.LevChi.val_rat_lt q hq h1
    have h3 : q.pr (incA D y) * q.pr (incA D y⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
    have h4 := congrArg (valuation K) h3
    rw [map_mul, map_one] at h4
    have h5 : valuation K (q.pr (incA D y)) * valuation K (q.pr (incA D y⁻¹)) < 1 :=
      (mul_le_of_le_one_right' h2.le).trans_lt hy
    exact (ne_of_lt h5) h4

theorem hasRes_of_pr {z : AE D} (c : 𝓞 D.host.E) (hz : valuation K (q.pr z - q.pr (incA D (c : D.host.E))) < 1) :
    GlobalTheory.Mem.Col2.HasRes PP (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z)) (Ideal.Quotient.mk PP.asIdeal c) := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : Valued.v (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) < 1 := by
    rw [← GlobalTheory.Mem.Col2.adAt_inclE D.host.F, ← map_sub, e, add_sub_cancel_left]
    exact valued_nat_mul_lt hr hN'
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    refine GlobalTheory.SeeSaw.LevChi.val_pr_lt q hq ?_
    have e2 : toEAf D (z - incA D y) = toEAf D z - Formalism.UG.inclE (FiniteAdeleRing (𝓞 D.host.F) D.host.F) y := by
      rw [RingHom.map_sub]
      rfl
    rw [e2, map_sub, GlobalTheory.Mem.Col2.adAt_inclE]
    exact h1
  have h3 : valuation K (q.pr (incA D (y - (c : D.host.E)))) < 1 := by
    have e3 : q.pr (incA D (y - (c : D.host.E))) = (q.pr z - q.pr (incA D (c : D.host.E))) - q.pr (z - incA D y) := by
      rw [map_sub, map_sub, map_sub]
      ring
    rw [e3]
    exact Valuation.map_sub_lt _ hz h2
  have h4 := val_lt_of_pr q hq h3
  refine ⟨c, rfl, ?_⟩
  have e4 : GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E c) =
      (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) +
        algebraMap D.host.E (PP.adicCompletion D.host.E) (y - (c : D.host.E)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [e4]
  refine Valuation.map_add_lt _ h1 ?_
  rw [valued_algebraMap]
  exact h4

end Split

end GlobalTheory.FamTrace.RedAt

namespace GlobalTheory.FamTrace.RedAt


end GlobalTheory.FamTrace.RedAt
