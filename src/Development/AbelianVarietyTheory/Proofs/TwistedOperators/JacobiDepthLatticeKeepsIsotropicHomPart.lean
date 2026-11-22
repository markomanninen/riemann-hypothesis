module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.SplitX

variable {D : D7}

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem mem_of_latV_top {S : HSp D} {L : Lat S} (hL : Submodule.IsFullLattice D.host.E L) (r : Fin S.rank → D.host.E)
    (h : (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * r i)) ∈ latV S L fun _ => True) : r ∈ L := by
  have h1 := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ h
  have e : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * r i)))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (r i) := by
    funext i
    rw [GlobalTheory.FinPlLoc.finPart_pair, one_mul]
    rfl
  rw [e] at h1
  let : Submodule.IsFullLattice D.host.E L := hL
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff (Submodule.IsLattice.fg D.host.E L) Submodule.IsFullLattice.span_eq_top r).1 h1

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {L : Lat V} {L₀ : Lat V₀}

theorem proj_latV_at {v : GlobalTheory.FinPl.Pl D} (hm : MonoAt d L L₀ v) {y : Fin V.rank → AE D} (hy : y ∈ latV V L (· = v)) :
    rat (d.e * d.qX) *ᵥ y ∈ latV V L (· = v) := by
  have h := ((hm y).1 hy).1
  have e : rat (d.e * d.qX) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) := by
    rw [show rat (d.e * d.qX) = d.jX ⬝ d.pX from rat_mul _ _, ← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => h i

theorem proj_mem (hL : Submodule.IsFullLattice D.host.E L) (hm : ∀ v, MonoAt d L L₀ v) (x : Fin V.rank → D.host.E)
    (hx : x ∈ L) : (d.e * d.qX) *ᵥ x ∈ L := by
  apply mem_of_latV_top hL
  have hy : (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * x i)) ∈ latV V L fun _ => True :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact (v.adicCompletionIntegers D.host.F).one_mem,
      fun v hv => (hv trivial).elim, 1, rfl, x, hx, rfl⟩
  have hz : rat (d.e * d.qX) *ᵥ (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * x i)) ∈
      latV V L fun _ => True := by
    refine (GlobalTheory.FinPlLoc.part_lat _ V L _ hL.toIsLattice).2 ⟨fun i => mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy) i, fun v _ e he => ?_⟩
    rw [← Matrix.mulVec_smul]
    exact proj_latV_at d (hm v) (GlobalTheory.FinPlLoc.smul_latV v he hy)
  rwa [GlobalTheory.SeeSaw.SplitLat.rat_mulVec_gen] at hz

end GlobalTheory.AscFin.SplitX

namespace GlobalTheory.AscFin.SplitX

variable {D : D7}

theorem hatMx_mul {m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} (π : Matrix (Fin n) (Fin n) D.host.E)
    (hM : ∀ x ∈ M, x * π ∈ M) {z : Mx D m n} (hz : z ∈ hatMx M) : z ⬝ rat π ∈ hatMx M := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * π, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] x i k) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] π k j) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.neg_mul]; exact neg_mem ha

theorem smul_homLat_mul {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (π : Matrix (Fin n) (Fin n) D.host.E) (hπ : ∀ y ∈ Λ, π *ᵥ y ∈ Λ) :
    ∀ x ∈ I • homLat Λ Λ', x * π ∈ I • homLat Λ Λ' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [Matrix.smul_mul]
    refine Submodule.smul_mem_smul hr (fun y hy => ?_)
    rw [← Matrix.mulVec_mulVec]
    exact hn _ (hπ y hy)
  · rw [Matrix.add_mul]; exact add_mem hx hy

end GlobalTheory.AscFin.SplitX


open GlobalTheory.AscFin.SplitX in
theorem GlobalTheory.AscFin.SplitX.latRow_extX : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), (F.dJ (σ + 1) h).extX _ (u ⬝ (F.dJ (σ + 1) h).jX) ∈ latRow G (2 * σ + 2) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h u hu
  have hmono : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => (((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).2.1 (σ + 1) h).2.1 v).2
  have hV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.sp.V_is (2 * (σ + 1) + 1) 0 (by omega) (by omega) (Nat.zero_le _)).sd
  have hW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (Nat.zero_le _)).sd
  have hπ := proj_mem (F.dJ (σ + 1) h) (selfDual_isFullLattice _ _ hV) hmono
  have hext : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ (F.dJ (σ + 1) h).jX) =
      u ⬝ rat ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) := by
    rw [HypDec.extX_apply, rat_mul, Matrix.mul_assoc]; rfl
  rw [hext]
  refine ⟨GlobalTheory.AscFinWit.latO_right (GlobalTheory.ChiGrid.isSelfDualC_neg hV) (GlobalTheory.ChiGrid.isSelfDualC_neg hV) hW _ hπ hu.1,
    fun e he => ?_⟩
  rw [← Matrix.smul_mul]
  exact hatMx_mul _ (smul_homLat_mul _ _ hπ) (hu.2 e he)
