module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignaturePosSmulBlockDiagonalReindexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvolutionHermitianSmulBlockDiagonalReinStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaledStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewFormStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat

theorem hasSig_blk {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA : Matrix (Fin a) (Fin a) ℂ) (GB : Matrix (Fin b) (Fin b) ℂ)
    {pa qa pb qb : ℕ} {κ : ℝ} (hκ : 0 < κ) (hA : Formalism.UG.HasSignature GA pa qa) (hB : Formalism.UG.HasSignature GB pb qb) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig ((κ : ℂ) • blk e GA GB) (pa + pb) (qa + qb) :=
  GlobalTheory.T.hasHermitianSignature_pos_smul_blockDiagonalReindexed e GA GB hκ hA hB

theorem isCartan_blk {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA sA : Matrix (Fin a) (Fin a) ℂ)
    (GB sB : Matrix (Fin b) (Fin b) ℂ) {κ : ℝ} (hκ : 0 < κ) (hA : IsCartanInv GA sA) (hB : IsCartanInv GB sB) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan ((κ : ℂ) • blk e GA GB) ((blk e sA sB).map conj) :=
  GlobalTheory.T.isCartanInvolutionHermitian_smul_blockDiagonalReindexed e GA sA GB sB hκ hA hB

theorem star_mem_AA {D : D7} {c : D.host.E} (hc : c ∈ D.host.AAbar) : star c ∈ D.host.AA :=
  GlobalTheory.T.star_mem_polarizationIdeal_of_mem_conj hc

theorem isLattice_pairLat {E : Type} [Field E] [NumberField E] {a b d : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)} (hA : Submodule.IsLattice E ΛA)
    (hB : Submodule.IsLattice E ΛB) (e : Fin a ⊕ Fin b ≃ Fin d) :
    Submodule.IsLattice E (pairLat (scLat 𝔞 ΛA) (scLat 𝔞 ΛB) e) :=
  GlobalTheory.T.isLattice_latticeBlockDirectSum_scaled h𝔞 hA hB e

theorem scLat_isFull {E : Type} [Field E] [NumberField E] {n : ℕ}
    {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {M : Submodule (𝓞 E) (Fin n → E)} (hM : Submodule.IsFullLattice E M) :
    Submodule.IsFullLattice E (scLat 𝔞 M) := by
  haveI := GlobalTheory.SkewLat.PairLatLattice.scLat_isLattice h𝔞 hM.toIsLattice
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr h𝔞)
  have ha' : a ∈ 𝔞 := ha
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro x _
  have hle : Submodule.span E (M : Set (Fin n → E)) ≤ Submodule.span E (scLat 𝔞 M : Set (Fin n → E)) := by
    apply Submodule.span_le.mpr
    intro y hy
    have hay : a • y ∈ scLat 𝔞 M := by
      intro c hc
      have hca : c * a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← inv_mul_cancel₀ h𝔞]
        exact FractionalIdeal.mul_mem_mul hc ha'
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hca
      rw [smul_smul, ← hr, algebraMap_smul]
      exact M.smul_mem r hy
    have := (Submodule.span E (scLat 𝔞 M : Set (Fin n → E))).smul_mem a⁻¹ (Submodule.subset_span hay)
    simpa [smul_smul, inv_mul_cancel₀ ha0] using this
  apply hle
  rw [Submodule.IsFullLattice.span_eq_top (self := hM)]
  trivial

theorem pairLat_isFull {E : Type} [Field E] [NumberField E] {a b d : ℕ}
    {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsFullLattice E M) (hN : Submodule.IsFullLattice E N)
    (e : Fin a ⊕ Fin b ≃ Fin d) : Submodule.IsFullLattice E (pairLat M N e) := by
  haveI := GlobalTheory.SkewLat.PairLatLattice.pairLat_isLattice hM.toIsLattice hN.toIsLattice e
  let φ : (Fin d → E) ≃ₗ[E] (Fin a → E) × (Fin b → E) :=
    (LinearEquiv.funCongrLeft E E e).trans (LinearEquiv.sumArrowLequivProdArrow _ _ E E)
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro x _
  have hle : Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set _) ≤
      (Submodule.span E (pairLat M N e : Set (Fin d → E))).comap φ.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    intro y hy
    apply Submodule.subset_span
    change φ.symm y ∈ pairLat M N e
    rw [mem_pairLat]
    simpa [φ, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow] using hy
  have hx : φ x ∈ Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set _) := by
    rw [GlobalTheory.SkewLat.PairLatLattice.prod_span_eq_top hM hN]
    trivial
  simpa using hle hx

theorem dual_pairLat {D : D7} (hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)}
    (hA : IsSelfDualC A ΛA) (hB : IsSelfDualC B ΛB) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E) :
    y ∈ pairLat (scLat D.host.AA ΛA) (scLat D.host.AA ΛB) e ↔ ∀ x ∈ pairLat (scLat D.host.AA ΛA) (scLat D.host.AA ΛB) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) :=
  GlobalTheory.T.scaledBlockSum_selfDual_traceSkewForm hc A B hA hB e y

theorem I_smul_skewGram_map {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (τ : D.what₂.Tau)
    (φ : D.host.E →+* ℂ) (hφ : ∀ x, φ x = conj (tauE D τ x)) :
    Complex.I • (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e).map φ =
      (((tauE D τ D.host.xi0).im : ℝ) : ℂ) • blk e (gramAt D A τ) (gramAt D B τ) := by
  have hre : (tauE D τ D.host.xi0).re = 0 := by
    have h := congrArg Complex.re (GlobalTheory.FockCompare.tauE_star τ D.host.xi0)
    rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, map_neg, Complex.neg_re, Complex.conj_re] at h
    linarith
  have hx : φ D.host.xi0 = -((((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I) := by
    rw [hφ]; apply Complex.ext <;> simp [hre]
  have hg : ∀ (S : HSp D) (k l : Fin S.rank), φ (S.gram l k) = tauE D τ (S.gram k l) := fun S k l => by
    rw [hφ, ← GlobalTheory.FockCompare.tauE_star]
    have h1 : S.gramᴴ = S.gram := Matrix.ext fun a b => S.herm.eq _ _
    have h2 := congrFun (congrFun h1 k) l
    rw [Matrix.conjTranspose_apply] at h2
    rw [h2]
  ext k l
  obtain ⟨k, rfl⟩ := e.surjective k
  obtain ⟨l, rfl⟩ := e.surjective l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, map_mul, hx]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases k with k | k <;> rcases l with l | l <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.transpose_apply, Matrix.zero_apply, map_zero, mul_zero, hg, Formalism.BasicNotions.TH.gramAt, Matrix.map_apply]
  all_goals linear_combination (-(((tauE D τ D.host.xi0).im : ℝ) : ℂ) * tauE D τ (HSpace.gram _ _ _)) * hI


open GlobalTheory.SkewLat in
theorem bigSpace_isSkew : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (e : Num G i j) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
      Spc.IsSkew D.sp.cm.sig B
        (Spc.mk (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) Λ (fun w => (blk e (W.cart (.grid (i : ℕ) ((j : ℕ) + 1)) (τf w)) (W.cart (.grid ((i : ℕ) + 1) (j : ℕ)) (τf w))).map conj) bas)
        ((spW G i j).rank + (spW₁ G i j).rank - ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2))
        ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) := by
  intro D T L sc G μ₀ hL W i j e B τf hB
  have hi := i.2
  have hj := j.2
  have hrV : Node.InRange D.R.m (.grid (i : ℕ) ((j : ℕ) + 1)) := ⟨by omega, by omega⟩
  have hrV₁ : Node.InRange D.R.m (.grid ((i : ℕ) + 1) (j : ℕ)) := ⟨by omega, by omega⟩
  have hV := GlobalTheory.FunObj.node_isV G hL hrV
  have hV₁ := GlobalTheory.FunObj.node_isV G hL hrV₁
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).1
  have hAA : D.host.AA ≠ 0 := fun h => by
    have := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h, mul_zero, zero_mul, zero_mul] at this
    exact zero_ne_one this
  set Λ := pairLat (scLat D.host.AA (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1)))) (scLat D.host.AA (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))) e
    with hΛ
  have hlat : Submodule.IsLattice D.host.E Λ := isLattice_pairLat hAA hV.sd.1 hV₁.sd.1 e
  have hfull : Submodule.IsFullLattice D.host.E Λ :=
    pairLat_isFull (scLat_isFull hAA (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hV.sd))
      (scLat_isFull hAA (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hV₁.sd)) e
  have hex : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ β := fun v => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Λ hcm
  classical
  refine ⟨Λ, fun v => if h : v ∈ B.P then (hex ⟨v, h⟩).choose else 1, ?skew, ?sig, hfull, ?dual, ?cartan, ?bas⟩
  case skew =>
    intro k l
    obtain ⟨k, rfl⟩ := e.surjective k
    obtain ⟨l, rfl⟩ := e.surjective l
    have hg : ∀ (S : HSp D) (a b : Fin S.rank), star (S.gram a b) = S.gram b a := fun S a b => by
      have h1 : S.gramᴴ = S.gram := Matrix.ext fun a b => S.herm.eq _ _
      have h2 := congrFun (congrFun h1 b) a
      rwa [Matrix.conjTranspose_apply] at h2
    show star (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e (e l) (e k)) = -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e (e k) (e l)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, Matrix.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply, star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D]
    rcases k with k | k <;> rcases l with l | l <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.zero_apply, star_zero, mul_zero, neg_zero, hg, neg_mul]
  case sig =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e).map (B.emb w).1) _ _
    rw [I_smul_skewGram_map _ _ e (τf w) (B.emb w).1 (hB w)]
    have hA := hV.sigOK (tauE D (τf w))
    have hA₁ := hV₁.sigOK (tauE D (τf w))
    rw [hV.sig] at hA
    rw [hV₁.sig] at hA₁
    have h := hasSig_blk e (gramAt D (spV G i j) (τf w)) (gramAt D (spV₁ G i j) (τf w)) (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) hA hA₁
    have hsum := h.1
    have hd : Fintype.card (Fin (spV G i j).rank ⊕ Fin (spV₁ G i j).rank) =
        Fintype.card (Fin ((spW G i j).rank + (spW₁ G i j).rank)) := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hd
    have h1 := hV.rank
    have h2 := hV₁.rank
    simp only [Node.rank, Node.neg] at h1 h2 h hsum
    convert h using 2 <;> omega
  case dual => exact fun y => dual_pairLat (fun c hc => star_mem_AA hc) _ _ hV.sd hV₁.sd e y
  case cartan =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e).map (B.emb w).1) _
    rw [I_smul_skewGram_map _ _ e (τf w) (B.emb w).1 (hB w)]
    exact isCartan_blk e _ _ _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (W.cart_is _ hrV (τf w)) (W.cart_is _ hrV₁ (τf w))
  case bas =>
    intro v
    show GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ (if h : (v : HeightOneSpectrum (𝓞 D.host.F)) ∈ B.P then (hex ⟨v, h⟩).choose else 1)
    rw [dite_eq_left v.2]
    exact (hex v).choose_spec

end GlobalTheory.SkewLat
