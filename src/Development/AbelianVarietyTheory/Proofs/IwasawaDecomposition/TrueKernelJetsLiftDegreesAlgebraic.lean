module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntAtOfLocTop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkThind
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPowClassNumber
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap


set_option maxHeartbeats 1000000 in
theorem jetC_th_mem_Qbar : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ)
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ColIn.JetsIn I →
    ∀ u μ i, i < B.R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1))
      (m : DVar (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) →₀ ℕ),
      (∀ τ, ∑ β, ∑ α, m (τ, β, α) = ∑ r, nuT (I.rec7 l Z) u i τ r) → jetC (O u μ).dgen ((O u μ).Th i c c') m ∈ Qbar := by
  classical
  intro B X I hOk hPins l Z Qp O hO hJ u μ i hi c c' m hm
  rw [hO.dgen, hO.Th]
  have hdeg : ∀ τ, (monoDeg m τ : ℤ) = nuDeg B u i τ := by
    intro τ
    rw [monoDeg_eq_sum, hm τ, Nat.cast_sum]
    unfold nuDeg
    refine Finset.sum_congr rfl fun r _ => ?_
    have e1 : ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℝ) = DV.nuRow (I.rec7 l Z) u (i + 1) τ r := (nu_t_identity (I.rec7 l Z) u i hi τ r).1
    have e2 := GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2
    have e3 := B.wts.nuW_eq u hi τ r
    have e4 := lamOf_wtN (B.wts.hc u τ) hi.le r
    have key : (((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) : ℝ) = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
      rw [Int.cast_natCast, e1, e2, ← Rat.cast_intCast, e3]
      unfold Wts.lamN at e3 ⊢
      rw [e4]
      rfl
    exact_mod_cast key
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth I hOk hPins l Z μ u i hi
  set p := (I.stp u μ i).rep c
  set p' := (I.stp u μ (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup μ) (I.cst μ) (I.idx μ) _ _ u i hX hPr
    hOk.sel_ok (hOk.T_mem u) hOk.g_mem (hOk.idx_ok μ) hi ⟨_, _, _, _, hOk.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  have span_of_self_dual {n : ℕ} {L : Submodule (𝓞 B.fields.E) (Sp B.fields.E n)} (hLat : IsSdLat L) :
      Submodule.span B.fields.E (L : Set (Sp B.fields.E n)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp B.fields.E n := fun i => star (f (Pi.single i 1))
    have hpair : hStd B.fields.E n v = f := by
      apply (Pi.basisFun B.fields.E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : B.fields.E) : r • v ∈ L := by
      rw [← show Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L = L from hLat.2, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd B.fields.E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd B.fields.E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := B.fields.E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      -- A nonzero coordinate would make the field finite over its ring of integers.
      let coord := (LinearMap.proj i : Sp B.fields.E n →ₗ[B.fields.E] B.fields.E).restrictScalars (𝓞 B.fields.E)
      have htop : L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.finite_def.mpr (htop ▸ hLat.1.fg.map coord)
      exact RingOfIntegers.not_isField B.fields.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  have hNfull : Submodule.IsFullLattice B.fields.E N :=
    { toIsLattice := hN.1, span_eq_top := span_of_self_dual hN }
  set cA := cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup μ) (I.cst μ) (I.idx μ) u i c.1 c'.1 p p'
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb μ u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hNfull hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb μ u) N N' cA cB hNfull hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u μ i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb μ u) N N')).comap (divLat cA (homAt (I.Sb μ u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb μ u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb μ u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl]
  have hsum := jetC_sum I.A.cD (fun q => I.A.σ₀ (Ξ (r q))) (fun q => I.A.thInd (I.Sb μ u) N N' cB (r q)) hs m
  have hchi : ∀ 𝔞, I.chi 𝔞 ≠ 0 := fun 𝔞 => by
    unfold ColIn.chi chiId
    exact Units.ne_zero _
  have hF0 : I.A.chiF _ _ N N' ≠ 0 := by
    show Th.chiFac B.host I.chi _ _ N N' ≠ 0
    unfold Th.chiFac
    exact mul_ne_zero (zpow_ne_zero _ (hchi _)) (zpow_ne_zero _ (hchi _))
  have hF : I.A.chiF _ _ N N' ∈ B.embLL.fieldRange := by
    show Th.chiFac B.host I.chi _ _ N N' ∈ B.embLL.fieldRange
    unfold Th.chiFac
    have hv := (GlobalTheory.Mem.ChiVal.chi_values B X I hOk).2
    exact mul_mem (zpow_mem (hv _) _) (zpow_mem (hv _) _)
  have hmem : (∑ q, I.A.σ₀ (Ξ (r q)) * jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m) ∈ B.embLL.fieldRange := by
    refine Subfield.sum_mem _ fun q _ => Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
    obtain ⟨y, hy⟩ := hJ.exists_eq (a := μ) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := m) hi
      ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ hdeg
    rw [← mul_inv_cancel_left₀ hF0 (jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m)]
    exact Subfield.mul_mem _ hF ⟨y, hy⟩
  have hQ : ∀ x ∈ B.embLL.fieldRange, x ∈ Qbar := by
    rintro _ ⟨y, rfl⟩
    exact mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y).algHom B.embLL.toRatAlgHom)
  show jetC I.A.cD (fun z => ∑ q, I.A.σ₀ (Ξ (r q)) * I.A.thInd (I.Sb μ u) N N' cB (r q) z) m ∈ Qbar
  rw [hsum]
  exact hQ _ hmem

end GlobalTheory.Mem.Col2.TC

end
