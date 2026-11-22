module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorFactorCoeffValuationLossLeAwayPrime
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

open GlobalTheory.MovedTwist GlobalTheory.MovedField Formalism.L2.Host GlobalTheory.ChiUnit in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorFactor_coeffValuationLossLe_awayPrime : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∉ ch.G.pl.W0 → ∀ (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    ∀ (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z) c := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β _ P hP w hw c _ hT z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  set q : ℕ := Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) with hqdef
  have hq0 : q ≠ 0 := (Formalism.EigenvalueLevelCeiling.plc_prime _).ne_zero
  have hq : (q : 𝓞 D.host.E) ∈ (P : Pl D.host.E).asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem _
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (P : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt P.1 (.inr ⟨t, P.2⟩))
  have hmu : ∀ j (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).mu j x : ℂˣ) : ℂ) := fun j x => by
    change UnitIn K q (((GlobalTheory.FunObj.muBase R.toLevCh j).loc P.1 x : ℂ) *
      ((R.xiH t).loc P.1 x : ℂ))
    refine UnitIn.mul ?_ ⟨(hK _).1 (hF.chars.xi t _ x), ?_⟩
    · rcases j with _ | j
      · exact unitIn_one K q
      · rw [GlobalTheory.FunObj.muBase]
        split_ifs with hj
        · obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf
          exact ⟨(hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x), unitOff_loc _ hn _ hq x⟩
        · exact unitIn_one K q
    · obtain ⟨n, hn, ho⟩ := hS.core.lev.xi_fin t
      refine unitOff_of_pow_eq_one q hn ?_
      have : ((R.toLevCh.xiH t) ^ n).loc P.1 x = 1 := by rw [show (R.toLevCh.xiH t) ^ n = 1 from ho]; rfl
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val this
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).chi i x : ℂˣ) : ℂ) :=
    fun i h1 h2 x => ⟨(hK _).1 (hF.chars.chi i h1 h2 _ x), unitOff_loc _ (ch.G.ch.inf i h1 h2) _ hq x⟩
  have heta : ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).eta x : ℂˣ) : ℂ) := fun x => by
    have hu := R.toLevCh.C.isEta.unr P.1
    obtain ⟨y, hy⟩ := hF.chars.eta P.1 hu
    exact ⟨loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x, unitOff_loc _ R.toLevCh.C.isEta.inf _ hq x⟩
  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).kappa e X x : ℂˣ) : ℂ) := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_mul_inv]
    refine UnitIn.mul ?_ ((heta x).pow _).inv
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw P.1)ˣ) (n : ℕ), UnitIn K q (apow x ((n : ℂ) / 2)) ∧ UnitIn K q (apow x (-(n : ℂ) / 2)) := fun x n =>
    ⟨⟨by simpa using apow_half_mem hsq x n, by simpa using unitOff_apow_half hq0 hq x n⟩,
      by simpa using apow_half_mem hsq x (-n), by simpa using unitOff_apow_half hq0 hq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, UnitIn K q ((locGrid ch.G t P).edgeFactor .one g e) := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact (((hkap e he _ _).mul (hkap e he _ _).inv).mul (hap _ _).1).mul (hap _ _).2
  have hk : keepAt ch.G (P : Pl D.host.E) = true := by
    classical
    simp [keepAt, hP]
  have hg := unitIn_prod _ _ (hedge ((repsAt ch.G t P).elt (β P)))
  simp only [moved, Grid.pathAct, hk, ite_true, one_mul]
  exact lossLe_unit_mul hw hg.1 hg.2 (hT _)
