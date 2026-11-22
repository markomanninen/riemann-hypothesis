module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittFlagUnipotentFixerFundamentalDomainLayers
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFlagUnipotentFixer_fundamentalDomain_layers : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → ∀ (vb : VolM D ρ V₀.rank) (ν : Measure (UX D ρ)), SFinite vb.μ → SFinite ν → IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ))) ((lC.prod (vb.μ.prod ν)).map e) := by
  intro D V V₀ ρ d e he lC 𝓒 _ _ hC vb ν _ _
  have : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  have : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).1
  have : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : DiscreteTopology (ratMx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.2.2.1
  have : Countable (ratMx D ρ V₀.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  have : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  have : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  have : MeasurableAdd₂ (skewA D ρ) := ⟨continuous_add.measurable⟩
  have rat_coords {b : Mx D ρ V₀.rank} {c : skewA D ρ}
      (h : d.nB b * d.nC c ∈ GQ V) : b ∈ ratMx D ρ V₀.rank ∧ c.1 ∈ ratMx D ρ ρ := by
    have hm := (mem_GQ_iff V _).1 h
    have hb : b ∈ ratMx D ρ V₀.rank := by
      have e1 : d.pX ⬝ (mt V (d.nB b * d.nC c) ⬝ d.j0) = b := by
        rw [mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc, d.pX_jX,
          Matrix.one_mul, zero_add]
      rw [← e1]
      exact ratMx_mul (rat_mem _) (ratMx_mul hm (rat_mem _))
    refine ⟨hb, ?_⟩
    have hc : d.nC c ∈ GQ V := by
      have := mul_mem (inv_mem (d.nB_mem_GQ hb)) h
      rwa [inv_mul_cancel_left] at this
    have hm2 := (mem_GQ_iff V _).1 hc
    have e2 : d.pX ⬝ (mt V (d.nC c) ⬝ d.jY) = c.1 := by
      rw [d.nC_jY, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, zero_add]
    rw [← e2]
    exact ratMx_mul (rat_mem _) (ratMx_mul hm2 (rat_mem _))
  have act_coords (c' c : skewA D ρ) (b' b : Mx D ρ V₀.rank) (u : GL (Fin ρ) (AE D)) :
      d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u)) =
        d.nC (c' + c + cComm V₀ b' b) * (d.nB (b' + b) * d.levi u) := by
    have h1 : d.nB b' * d.nC c = d.nC c * d.nB b' := (d.nC_mul_nB b' c).symm
    have h2 : d.nB (b' + b) * d.nC (cComm V₀ b' b) = d.nC (cComm V₀ b' b) * d.nB (b' + b) :=
      (d.nC_mul_nB _ _).symm
    calc d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u))
        = d.nC c' * (d.nB b' * d.nC c) * d.nB b * d.levi u := by simp only [mul_assoc]
      _ = d.nC c' * d.nC c * (d.nB b' * d.nB b) * d.levi u := by rw [h1]; simp only [mul_assoc]
      _ = d.nC c' * d.nC c * d.nC (cComm V₀ b' b) * d.nB (b' + b) * d.levi u := by
          rw [d.nB_mul_nB, h2]; simp only [mul_assoc]
      _ = d.nC (c' + c + cComm V₀ b' b) * (d.nB (b' + b) * d.levi u) := by
          rw [d.nC_add, d.nC_add]; simp only [mul_assoc]
  have mem_radX_iff (n : GA D V) : n ∈ radX d ↔ ∃ b c, n = d.nB b * d.nC c := by
    constructor
    · intro hn
      obtain ⟨hf, hx⟩ := Subgroup.mem_inf.1 hn
      obtain ⟨⟨c, b, u⟩, hu⟩ := e.surjective ⟨n, hf⟩
      have hn' : n = d.nC c * (d.nB b * d.levi u.1) :=
        (congrArg Subtype.val hu).symm.trans (he (c, b, u))
      change mt V n ⬝ d.jX = d.jX at hx
      have hX : mt V n ⬝ d.jX = d.jX ⬝ u.1.1 := by
        rw [hn', mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jX,
          ← Matrix.mul_assoc (mt V (d.nB b)), d.nB_jX,
          ← Matrix.mul_assoc (mt V (d.nC c)), d.nC_jX]
      have hmat : d.pX ⬝ (d.jX ⬝ u.1.1) = d.pX ⬝ d.jX :=
        congrArg (fun X => d.pX ⬝ X) (hX.symm.trans hx)
      rw [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at hmat
      have hu' : u.1 = 1 := Units.ext hmat
      exact ⟨b, c, by rw [hn', hu', map_one, mul_one, d.nC_mul_nB]⟩
    · rintro ⟨b, c, rfl⟩
      refine Subgroup.mem_inf.2 ⟨mul_mem (d.nB_mem_NFlag b) (d.nC_mem_NFlag c), ?_⟩
      change mt V (d.nB b * d.nC c) ⬝ d.jX = d.jX
      rw [mt_mul, Matrix.mul_assoc, d.nC_jX, d.nB_jX]
  have hκ : ∀ b' : Mx D ρ V₀.rank, Measurable (cComm V₀ b') := by
    intro b'
    have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
    have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
    have h1 : Continuous fun b : Mx D ρ V₀.rank => half D • (b ⬝ plus V₀ b' - b' ⬝ plus V₀ b) :=
      ((continuous_id.matrix_mul continuous_const).sub (continuous_const.matrix_mul hp)).const_smul (half D)
    exact (h1.subtype_mk _).measurable
  have key : ∀ (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) (p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ)),
      d.nC c' * d.nB b' * (e p : GA D V) = (e (c' + p.1 + cComm V₀ b' p.2.1, b' + p.2.1, p.2.2) : GA D V) := by
    intro c' b' p
    rw [he p, he (c' + p.1 + cComm V₀ b' p.2.1, b' + p.2.1, p.2.2)]
    exact act_coords c' p.1 b' p.2.1 p.2.2.1
  have hsm : ∀ (g : ↥((GQ V ⊓ radX d).subgroupOf (flagN d))) (x : flagN d),
      ((g • x : flagN d) : GA D V) = ((g : flagN d) : GA D V) * (x : GA D V) := fun _ _ => rfl
  refine GlobalTheory.Layers.isFundamentalDomain_layers (mA := lC) (mB := vb.μ) (ν := ν) ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) (ratMx D ρ V₀.rank) (cComm V₀) hκ e
    ?_ ?_ ?_ hC vb.covol.2.1
  · intro g g' x h
    rw [Subgroup.smul_def, Subgroup.smul_def] at h
    exact Subtype.ext (mul_right_cancel h)
  · rintro ⟨⟨γ, hγN⟩, hγ⟩
    rw [Subgroup.mem_subgroupOf] at hγ
    obtain ⟨b, c, hbc⟩ := (mem_radX_iff γ).1 (Subgroup.mem_inf.1 hγ).2
    subst hbc
    have hr := rat_coords (Subgroup.mem_inf.1 hγ).1
    refine ⟨⟨c, AddSubgroup.mem_addSubgroupOf.2 hr.2⟩, ⟨b, hr.1⟩, fun p => Subtype.ext ?_⟩
    rw [Subgroup.smul_def]
    have h := key c b p
    rw [d.nC_mul_nB] at h
    exact h
  · rintro ⟨c', hc'⟩ ⟨b', hb'⟩
    have hrad : d.nC c' * d.nB b' ∈ radX d := (mem_radX_iff _).2 ⟨b', c', d.nC_mul_nB b' c'⟩
    have hQ : d.nC c' * d.nB b' ∈ GQ V :=
      mul_mem (d.nC_mem_GQ (AddSubgroup.mem_addSubgroupOf.1 hc')) (d.nB_mem_GQ hb')
    have hN : d.nC c' * d.nB b' ∈ flagN d := (Subgroup.mem_inf.1 hrad).1
    let g : ((GQ V ⊓ radX d).subgroupOf (flagN d)) :=
      ⟨⟨d.nC c' * d.nB b', hN⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hQ, hrad⟩)⟩
    refine ⟨g, fun p => Subtype.ext ((hsm g (e p)).trans (key c' b' p))⟩
