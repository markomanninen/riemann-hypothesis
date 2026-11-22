module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
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
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdemSumLeft
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
public import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.Fam.LevelFrames


open _root_.Formalism.L2.Col in
theorem redV_eq_of_near {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ i j : Fin n, P.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1)
    {y : Sp E n} (hy : y ∈ stdAt E n P) : redV P (f y) = redV P y := by
  funext i
  have hy' := GlobalTheory.TopStep.mem_stdAt.1 hy
  have e : f y i - y i = ∑ j, (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) * y j := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ← Fin.ext_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h : P.valuation E (f y i - y i) < 1 := by
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((GlobalTheory.AtTypeExists.intAt_iff _ _).1 (hy' j))) (hf i j)
  obtain ⟨h1, h2⟩ := twRed0_of_val P h
  have h3 := reduction_add h1 (hy' i)
  rw [sub_add_cancel, h2, zero_add] at h3
  exact h3


end GlobalTheory.Fam.LevelFrames
