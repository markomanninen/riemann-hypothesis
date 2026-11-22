module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareSystemPolarVanishingStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergenceStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquarePolarIntegralIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolarIdentityFromSymmetricFormsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_polar {σ : Type} [Fintype σ] {n : ℕ} {α : Type} {l : Filter α} {f : α → (Fin n → σ) → ℝ}
    {a : (Fin n → σ) → ℝ} (c : Fin n → σ → ℝ) (h : ∀ w, Tendsto (fun t => f t w) l (𝓝 (a w))) :
    Tendsto (fun t => polar n (f t) c) l (𝓝 (polar n a c)) := by
  unfold polar
  exact tendsto_finsetSum _ fun w _ => (h w).const_mul _

theorem Realis.limNum_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type}
    {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) {II : IntersectionSystem}
    (hII : IsFullIntersectionSystem II) (hpos : 0 < S.t₀) (π : Equiv.Perm (Fin (D + 1)))
    (w : Fin (D + 1) → σ) : Re.limNum II (w ∘ π) = Re.limNum II w := by
  have hev : (fun t => Re.num II t (w ∘ π)) =ᶠ[𝓝[>] 0] fun t => Re.num II t w := by
    filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
    have h := (hII.1 K ι).1 P (D + 1) (fun j => Re.line (w j) t) π Re.arith
      fun j => Re.line_smooth _ t ht.1 ht.2
    unfold Realis.num
    exact congrArg (· / (Re.deg : ℝ)) h
  unfold Realis.limNum limUnder
  rw [Filter.map_congr hev]

theorem AnSys.degNum_perm {e : ℕ} {σ : Type} (S : AnSys e σ) (π : Equiv.Perm (Fin e)) (w : Fin e → σ) :
    S.degNum (w ∘ π) = S.degNum w :=
  ReciprocityTheory.AnForm.M.mIntSymm S.A (fun j => S.th (w j)) π fun _ => 1

theorem thmA_limit : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  intro hI hF II hII K _ ι _ d σ _ SY P Re a₀ ε Q c hc u
  have hpos : 0 < SY.t₀ := (SY.reg a₀).1
  have hposW : 0 < Q.an.SW.t₀ := (Q.an.SW.reg none).1
  obtain ⟨C₃, s₀, -, hAg⟩ := GlobalTheory.T.agreement_positive hI (d + 1) σ SY 0 hpos
  have hlim := (hAg II hII K ι P Re).1
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ Q.an.SW.t₀ := by
    filter_upwards [Ioc_mem_nhdsGT hposW] with t ht using ⟨ht.1, ht.2⟩
  refine GlobalTheory.T.polar_identity_from_symmetric_forms σ (d + 1) (Re.limNum II) SY.degNum kappa ε a₀ (Re.limNum_perm hII hpos)
    SY.degNum_perm (fun n hn => ?_) c hc u
  have hsq := GlobalTheory.T.square_system_polar_vanishing hI II hII K ι d σ SY P Re a₀ ε Q n hn
  refine ⟨?_, fun k hk hk2 => ?_⟩
  · have h1 := tendsto_polar (fun _ (x : σ) => (n x : ℝ)) hlim
    have h2 : Tendsto (fun t => polar (d + 2) (Re.num II t) fun _ (x : σ) => (n x : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).1.symm)
    exact tendsto_nhds_unique h1 h2
  · have h1 := tendsto_polar (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) hlim
    have h2 : Tendsto (fun t => -∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t))
          (Q.an.wcoef (fun a => (n a : ℝ)) k i)) (𝓝[>] 0)
        (𝓝 (-∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potH (w r)) Q.an.gH)
          (Q.an.wcoef (fun a => (n a : ℝ)) k i))) :=
      (tendsto_finsetSum _ fun i _ => tendsto_polar _ fun w =>
        (GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε Q.an w).2).neg
    have h3 := tendsto_nhds_unique (h1.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).2 k hk hk2)) h2
    let square := Q.an
    let coeff : σ → ℝ := fun a => (n a : ℝ)
    have hcoeff : coeff a₀ = 0 := by simp [coeff, hn]
    have hIntegralIdentity :
        ∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt square.SW.A (fun r => square.SW.potH (w r)) square.gH)
          (square.wcoef coeff k i) =
        2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) := by
      have hSquareLim :=
        GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε square
      obtain ⟨-, hnW, hC2W, -, -⟩ := anSys_open_basics (d + 2) (Option σ) square.SW
      obtain ⟨-, hnY, hC2Y, -, -⟩ := anSys_open_basics (d + 1) σ SY
      have hhom (w : Fin (d + 1) → σ) :
          MIntegrable SY.A (fun i => SY.potH (w i)) (fun _ => 1) ∧
            mInt SY.A (fun i => SY.potH (w i)) (fun _ => 1) = SY.degNum w := by
        let : MeasurableSpace SY.X := borel SY.X
        have : BorelSpace SY.X := ⟨rfl⟩
        have hlim := hI.convergenceSigned SY.A SY.Θ SY.L SY.s SY.m SY.W
          SY.potΘ SY.posΘ SY.potL SY.sec SY.snc SY.norm_le
          (fun i => SY.th (w i)) (fun i => SY.ph (w i)) (fun i => SY.phT (w i)) SY.C₅ SY.C SY.t₀
          (fun i => SY.sing (w i)) (fun i => SY.reg (w i)) (fun i => SY.c2 (w i))
          (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
          (fun _ y _ => SY.abs_one_le_log_rW y)
          (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
            refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
            exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
        refine ⟨hlim.1, ?_⟩
        have hDegree : Tendsto (fun t => mInt SY.A (fun i => SY.potT (w i) t) (fun _ => 1))
            (𝓝[>] 0) (𝓝 (SY.degNum w)) :=
          tendsto_const_nhds.congr' (by
            filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
            exact (ReciprocityTheory.AnForm.M.massIndep SY.A (fun i => SY.th (w i))
              (fun i => SY.phT (w i) t) (fun i => (SY.sing (w i)).1)
              (fun i => ((SY.reg (w i)).2.2 t ht.1 ht.2).1)).symm)
        exact tendsto_nhds_unique hlim.2 hDegree

      have hexW := fun i => mInt_sumPot_expand (d + 2) square.SW.X square.SW.A (Option σ) square.SW.open' square.SW.potH
        (square.wcoef coeff k i) square.gH hnW hC2W fun w => (hSquareLim w).1
      have hexY := mInt_sumPot_expand (d + 1) SY.X SY.A σ SY.open' SY.potH
        (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) (fun _ => 1) hnY hC2Y fun w => (hhom w).1
      have hpolW : ∀ i, polar (d + 2) (fun w => mInt square.SW.A (fun r => square.SW.potH (w r)) square.gH) (square.wcoef coeff k i) =
          mInt square.SW.A (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH := fun i => (hexW i).2.symm
      have hpolY : polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) =
          mInt SY.A (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (fun _ => 1) := by
        rw [hexY.2]
        exact Finset.sum_congr rfl fun w _ => by rw [(hhom w).2]

      have hoW : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ square.U n → square.ΦW n z ∈ square.SW.open' := by
        intro n z hz
        rw [square.bdry_eq 0, Set.mem_preimage, square.first_projection_chart_compat n z hz]
        exact square.ΦY_open n _ (by simpa using hz)

      have hcW := fun i => integrableOn_hasSum_paramCover (d + 2) square.SW.X square.SW.A _ _ square.ΦW
        (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH square.coverW
        (fun n z hz r => SqFubini.isC2At_sumPot _ _ _ _ fun a => hC2W a _ (hoW n z (square.B_meas n |>.2 hz)))
        (hexW i).1
      have hcY := integrableOn_hasSum_paramCover (d + 1) SY.X SY.A _ _ square.ΦY
        (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (fun _ => 1) square.coverY
        (fun n z hz r => SqFubini.isC2At_sumPot _ _ _ _ fun a => hC2Y a _ (square.ΦY_open n z (square.B_meas n |>.2 hz)))
        hexY.1

      have hFibreIntegral : ∀ n, ∑ i ∈ Finset.range k,
          ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n},
          square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z =
          2 * kappa k * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n},
            (fun _ => (1 : ℝ)) (square.ΦY n z) * paramDens
              (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z := by
        intro n
        let α : (Fin d → ℂ) → ℝ := fun y => ∑ a, coeff a * square.α n a y
        have hd := GlobalTheory.T.square_parametrized_density_formula d σ SY a₀ ε square coeff hcoeff n k hk hk2
        have hmW : MeasurableSet {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n} := (square.coverW.2.1 n).1
        have hmY : MeasurableSet {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n} := (square.coverY.2.1 n).1
        let F : ℕ → (Fin (d + 2) → ℂ) → ℝ := fun i z =>
          logSin (square.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) * maDens (SqFubini.EW (square.G n) α k i) z
        have hae : ∀ i < k, ∀ᵐ z ∂(volume.restrict {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n}),
            square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z = F i z := by
          intro i hi
          filter_upwards [ae_restrict_of_ae (SqFubini.ae_ne d), ae_restrict_mem hmW] with z hne hz
          have hU : Fin.tail (Fin.tail z) ∈ square.U n := (square.B_meas n).2 hz
          have h1 : square.gH (square.ΦW n z) = logSin (square.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) :=
            square.norm_hom n z hU hne
          have h2 : paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z =
              maDens (SqFubini.EW (square.G n) α k i) z := hd.2 i hi z hU
          rw [h1, h2]
        have hH : ∀ z ∈ {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n},
            (fun _ => (1 : ℝ)) (square.ΦY n z) * paramDens
              (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z =
            maDens (SqFubini.EY (square.G n) α k) z := by
          intro z hz
          have h2 : paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z =
              maDens (SqFubini.EY (square.G n) α k) z := hd.1 z ((square.B_meas n).2 hz)
          rw [h2, one_mul]
        have hFint : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n} :=
          fun i hi => ((hcW i).1 n).congr (hae i hi)
        have hHint : IntegrableOn (maDens (SqFubini.EY (square.G n) α k)) {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n} :=
          (integrableOn_congr_fun hH hmY).1 (hcY.1 n)
        have hpt : ∀ y ∈ square.B n, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
            (2 * kappa k) * ∫ a : ℂ, maDens (SqFubini.EY (square.G n) α k) (Fin.cons a y) := by
          intro y hy
          have hyU : y ∈ square.U n := (square.B_meas n).2 hy
          have hnh : square.U n ∈ 𝓝 y := (square.U_open n).mem_nhds hyU
          have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := ENat.LEInfty.out
          exact GlobalTheory.T.log_sine_monge_ampere_integral hF d k hk hk2 (square.G n) α y
            (by filter_upwards [hnh] with y' hy' using square.G_pos n y' hy')
            (fun p q => ((square.G_smooth n p q).contDiffAt hnh).of_le h2)
            (ContDiffAt.sum fun a _ => contDiffAt_const.mul (((square.α_smooth n a).contDiffAt hnh).of_le h2))
        rw [Finset.sum_congr rfl fun i hi => integral_congr_ae (hae i (Finset.mem_range.1 hi)),
          setIntegral_congr_fun hmY hH]
        exact SqFubini.fibre_sum (square.B n) F _ _ hFint hHint hpt (square.B_meas n).1
      have hsW : HasSum (fun n => ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n},
          square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z)
          (∑ i ∈ Finset.range k, mInt square.SW.A (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH) :=
        hasSum_sum fun i _ => (hcW i).2
      rw [funext hFibreIntegral] at hsW
      rw [Finset.sum_congr rfl fun i _ => hpolW i, hpolY]
      exact hsW.unique (hcY.2.mul_left _)
    rw [h3, hIntegralIdentity]
    ring

end GlobalTheory.CompanionTheory.Ar.PB
