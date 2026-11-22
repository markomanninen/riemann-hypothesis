module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
public import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
public import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesSpanCuspFormsWeightStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIndexBoundHypothesesAtInstanceStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeightStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProofStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeightModuleIsLatticeOfShortSeriesSpanStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthSumRecord
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem log_DF_le_of_rows {D : D7} {j : ℕ} (large₂ : SizeData₂ D) (ka w : WeightFamilies.Wt D j) (h3 : 3 ≤ DF w) (hle : DF w ≤ DF ka)
    (hrow : Real.log (1 + DF ka) ≤ 2 * large₂.sc.L) : Real.log (DF w) ≤ 2 * large₂.sc.L := by
  have hpos : (0 : ℝ) < (DF w : ℝ) := by
    have h0 : 0 < DF w := by omega
    exact_mod_cast h0
  have hmono : (DF w : ℝ) ≤ 1 + (DF ka : ℝ) := by
    have h1 : (DF w : ℝ) ≤ (DF ka : ℝ) := by exact_mod_cast hle
    linarith
  exact (Real.log_le_log hpos hmono).trans hrow


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem hypC_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 (nusR h j wL) ∧ LatAt (recB h.toLawsCore) j ka ∧ (∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w) ∧ PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) wL ∧ ∃ Sh : Finset ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j wF)) = ⊤ ∧ ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (gcR large₂ (recB h.toLawsCore)) := by
  intro D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpar hpage
  have hj1 : 1 ≤ j := hj.1
  have hjm : j ≤ D.R.m := hj.2
  obtain ⟨hParA, hSetC, -, -, -⟩ := hpage.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hnW, -, hIsL, hIsF, -⟩ := hSetC
  have hchart := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hgam : GlobalTheory.RunIn.GamAt T.toCore := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  have hrows := (GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hpage.hyp hpage.page hpage.ck).1
  have hwb := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hj1 hpage.hyp
  have hLle : DF wL ≤ DF ka := (hwb.1 wL (by simp)).1
  have hlogL : Real.log (DF wL) ≤ 2 * large₂.sc.L :=
    log_DF_le_of_rows large₂ ka wL hpage.df hLle hrows.2.2.2.2.2.2.2.1
  have hn : 2 * D.R.f * D.R.r ≤ wL.n := by
    rw [hIsL.1]
    have hr : 2 ≤ D.R.r + 1 := by have := hpage.r8; omega
    calc 2 * D.R.f * D.R.r = D.R.f * D.R.r * 2 := by ring
      _ ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ hr
      _ ≤ nW := hnW
  have hH1 := (GlobalTheory.DepthSum.depth_sum_record D T h j hj large₂ wL hn hlogL).1
  have hown : FamilyHypotheses.OwnPr D p := by
    obtain ⟨q, hq, hall⟩ := hpar.sh.dPd
    have e : p = q := (hpar.own 0).symm.trans (hall j hj 0)
    subst e
    exact hq
  have hH2 := (GlobalTheory.T.scaledRunLattices_in_supLattices D T h hpar.sh j hj hinj EX hpar.orient p hpar.own ka wL wF Tn nP hIsF).1
  have hth : ∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w :=
    fun w => GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight D T h j hj hinj EX hpar.orient w
  have helper : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GlobalTheory.RunIn.GamAt T.toCore → LawsSh T → 0 < badN D → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → (∀ w2, IsG2 wL wF w2 → GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w2) → (j < D.R.m → ∀ w1, IsDoubledWeightWithShift wL w1 nW → GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w1) → H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → (∀ nus, EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → EtaleWeightGaps.HypC large₂ (recPJ h j hj) H C2 A2 CR 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 nus) ∧ ∃ (G₀ : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF) (Sh : Finset ((recB h.toLawsCore).Cusp j wF)), Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j wF)) = ⊤ ∧ G₀.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw ∧ NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G₀.w i).1) ∧ ∀ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc := by
    suffices hInputs : _ by exact hInputs
    intro hCI D T h hGam hSh hbad hA1 hUX hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw
      hOwn hHP hPA hCK hThG2 hThG1 hH2 hG4 hPrw
  
    obtain ⟨hRows, h16⟩ := GlobalTheory.T.sizePageRows_of_sizePageAt D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP
      nW h0 hHP hPA hCK
  
    obtain ⟨hW, hWn, -, -⟩ := GlobalTheory.RunWeights.weights_below D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂ H C2 A2 CR CT
      ka wL wF Tn nP nW h0 hj.1 hHP
  
    have hSpan : ∀ w, w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)) →
        8 * D.R.f * D.R.r + 4 ≤ w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w := fun w hw hn =>
      GlobalTheory.T.shortThetaSeries_span_cuspForms_weight hCI D T h hSh hGam hbad hUX j hj.1 hj.2 w
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w (hW w hw).2.2.2) hn
    have hSB := GlobalTheory.T.runScalars_nonzero_bounded_supBound hCI D T h hGam hSh hA1 hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hOwn hHP hRows
      (hSpan wF (by simp) (hWn wF (by simp))) (hSpan _ (by simp) (hWn _ (by simp))) (hSpan ka (by simp) (hWn ka (by simp)))
    have hI4 := GlobalTheory.T.exists_integral_auxiliary_cuspForms_supBound hCI D T h hGam hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hRows h16 hThG2 hThG1
  
    have hThL : GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX wL := by
      have hW0 := hH2.1
      rw [GlobalTheory.RunIn.sW_eq_sOf] at hW0
      exact hW0
    obtain ⟨G₀, hG₀⟩ := GlobalTheory.T.exists_runData_generating_scaled_thetaLattice_weight hCI D T h hGam hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hHP hRows
      hThL hG4 hPrw
    obtain ⟨Sh, hSh', -, hTh⟩ := GlobalTheory.exists_short_span_thetaTie_of_scalars D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂
      H.C1 H.A1 Gc (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn hSB hG4
    have hsW : (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sW ≠ 0 := by
      rw [GlobalTheory.RunIn.sW_eq_sOf]
      exact (GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL).1
    refine ⟨fun nus hnus => (FamilyHypotheses.hypC_iff large₂ (recPJ h j hj) H C2 A2 CR CT _ ka wL wF Tn nP nW h0 nus).2
        ⟨hHP, hSB, hnus, hH2, hI4⟩, G₀, Sh, hSh', hG₀, ?_, hTh⟩
    exact GlobalTheory.T.scaledThetaLattice_generators_noCommonZero hCI D T h EX j hj _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hHP hsW G₀ hG₀
  have main := helper hchart D T h hgam hpar.sh hpar.bad hpar.lvA hpar.same hinj EX p j hj large₂ H C2 A2 7 CT
    ka wL wF Tn nP nW h0 (gcR large₂ (recB h.toLawsCore)) (38 * large₂.sc.L + PO D large₂) hown hpage.hyp hpage.page hpage.ck
    (fun w2 _ => hth w2) (fun _ w1 _ => hth w1) hH2 (growthConstantBound_gcR large₂ _) le_rfl
  have hC := main.1 _ hH1
  obtain ⟨-, Sh, hspan, -, -, hTied⟩ := main.2
  have hsK := hC.2.2.1.2.2.2.1
  have hspanka := GlobalTheory.T.shortThetaSeries_span_cuspForms_weight hchart D T h hpar.sh hgam hpar.bad hpar.same j hj1 hjm ka
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj ka (hwb.1 ka (by simp)).2.2.2) (hwb.2.1 ka (by simp))
  have hlat := GlobalTheory.T.weightModule_isLattice_of_shortSeries_span D T.toCore h.toLawsCore hgam large₂ H.CA hParA j ka _ (recPJ h j hj) _ wL wF hsK hspanka
    hC.2.2.2.2.1
  refine ⟨hC, hlat, hth, ⟨hpage.p13, fun σ => ?_, hpage.frd, hpage.r8, hpage.df⟩, Sh, hspan, hTied⟩
  rw [GlobalTheory.RunIn.sW_eq_sOf]
  exact ((GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D _ hinj EX j wL).2 σ).2.2.1

end GlobalTheory.RunJoin
