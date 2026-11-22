module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.BesSemi

variable {D : D7}

theorem continuous_embA {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Continuous (embA d o) := by
  have h : (embA d o : GA D A → GA D S) = fun h => d.emb0 (o.emb (h, 1)) := funext fun h => embA_apply d o h
  rw [h]
  exact d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))

theorem besselCompression_unipotent_mul_embedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 * (mt S (n * d.emb0 k) * d.j0) = mt S₀ k := by
  have hflag := (GlobalTheory.BesselChar.mem_NFlag_iff S d.e
    (GlobalTheory.MixPer.Decomp.linInd d) n).1 hn
  have hcols : ∀ j : Fin S₀.rank, ∃ a : Fin ρ → AE D,
      mt S n *ᵥ (fun i => d.j0 i j) = (fun i => d.j0 i j) + d.jX *ᵥ a := by
    intro j
    apply hflag.2
    change d.pY *ᵥ (fun i => d.j0 i j) = 0
    funext i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (congrFun d.pY_j0 i) j
  choose a ha using hcols
  have h0 : mt S n * d.j0 = d.j0 + d.jX * Matrix.of (fun i j => a j i) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (ha j) i
  have hproj : d.p0 * (mt S n * d.j0) = 1 := by
    rw [h0, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic,
    ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, hproj, Matrix.one_mul]

theorem unique {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n n' : GA D S}
    (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) {h h' : GA D A} (e : n * embA d o h = n' * embA d o h') :
    n = n' ∧ h = h' := by
  have e0 := congrArg (fun g => d.p0 * (mt S g * d.j0)) e
  rw [embA_apply, embA_apply, besselCompression_unipotent_mul_embedding d hn,
    besselCompression_unipotent_mul_embedding d hn'] at e0
  have hh : h = h' := congrArg Prod.fst (o.emb_injective (mt_injective S₀ e0))
  subst h'
  exact ⟨mul_right_cancel e, rfl⟩

theorem rat_iff {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n : GA D S}
    (hn : n ∈ flagN d) (h : GA D A) : n * embA d o h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ A := by
  constructor
  · intro hg
    have hk : o.emb (h, 1) ∈ GQ S₀ := by
      rw [mem_GQ_iff]
      rw [embA_apply] at hg
      rw [← besselCompression_unipotent_mul_embedding d hn]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S _).1 hg) (rat_mem _))
    have hA : h ∈ GQ A := by
      rw [mem_GQ_iff]
      have e : o.pA * (mt S₀ (o.emb (h, 1)) * o.jA) = mt A h := by
        rw [o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]
      rw [← e]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S₀ _).1 hk) (rat_mem _))
    have he : embA d o h ∈ GQ S := by rw [embA_apply]; exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hk
    refine ⟨?_, hA⟩
    have : n = n * embA d o h * (embA d o h)⁻¹ := (mul_inv_cancel_right n _).symm
    rw [this]
    exact mul_mem hg (inv_mem he)
  · rintro ⟨hn', hA⟩
    refine mul_mem hn' ?_
    rw [embA_apply]
    exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (o.emb_mem_GQ hA (one_mem _))

end GlobalTheory.Unf.BesSemi

namespace GlobalTheory.Unf

theorem besSemi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  intro D σ B
  refine ⟨BesSemi.continuous_embA B.d B.o, GlobalTheory.Mem.TrueRecord.isClosed_NFlag B.V (isIsoSub_e B.d),
    fun n hn h => ?_, fun n hn n' hn' h h' e => BesSemi.unique B.d B.o hn hn' e,
    fun n hn h => BesSemi.rat_iff B.d B.o hn h⟩
  rw [embA_apply]
  let g := B.d.emb0 (B.o.emb (h, 1))
  have hg : mt B.V g * B.d.e.map (incA D) = B.d.e.map (incA D) :=
    B.d.wittDecomp_anisotropicEmbedding_inclX _
  have hg' := GlobalTheory.BesselChar.inv_fix_cols (mt_inv_mul B.V g) hg
  have hflag := GlobalTheory.BesselChar.mem_NFlag_iff B.V B.d.e
    (GlobalTheory.MixPer.Decomp.linInd B.d)
  change g * n * g⁻¹ ∈ flagN B.d
  apply (hflag _).2
  rw [mt_mul, mt_mul]
  exact ((hflag n).1 hn).conj hg hg' (mt_mul_inv B.V g)
    (GlobalTheory.BesselChar.perp_fixed B.d.e g⁻¹ hg')

end GlobalTheory.Unf
