module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.UnramDict

theorem fixed_of_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  intro L _ _ _ n F U hU v w hw U0 hU0 σ b hb p hp φ hφU hfix x hK
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  have hK1 : (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf.1 hK).2
  have hK2 : cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have h : cLoc w x.val = b * (p x).val * b⁻¹ := by rw [hp]; group
    rw [h]
    exact mul_mem (mul_mem hb hK1) (inv_mem hb)
  have hx := x.2
  obtain ⟨y, hy⟩ := F.onto x.val (Subgroup.mem_inf.1 hx).1
  have hyU : y ∈ Umax L n := fun i j => mem_ALint F _ fun u => by
    rw [← F.loc, hy]
    exact cLoc_entry_mem hx hK2 u i j
  have hk (a : L) (z : AFplus L) :
      F.κ.toRingHom (a ⊗ₜ[maximalRealSubfield L] z) =
        algebraMap L _ a * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
    have h1 (z : AFplus L) : F.κ (1 ⊗ₜ z) =
        GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
      refine FiniteAdeleRing.ext _ fun q => ?_
      obtain ⟨i, hi, hia⟩ := F.right q (q.under (𝓞 (maximalRealSubfield L))) rfl
      rw [hia]
      change i (z (q.under (𝓞 (maximalRealSubfield L)))) = GlobalTheory.LFun.complMap rfl (z (q.under (𝓞 (maximalRealSubfield L))))
      refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
        (q.under (𝓞 (maximalRealSubfield L)))).equalizer hi
        (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k => ?_)) _
      change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
      rw [GlobalTheory.LFun.complMap_algebraMap]
      have he : (algebraMap (maximalRealSubfield L) (AFplus L) k) (q.under (𝓞 (maximalRealSubfield L))) =
          algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (q.under (𝓞 (maximalRealSubfield L)))) k := rfl
      rw [← he, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
      rfl
    rw [← h1, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have hc (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L)
      (hz : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 (maximalRealSubfield L)) = v → F.κ z u = 0) :
      compAt L v z = 0 :=
    (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) hk v z).2 hz
  have hyt : TrivOutside {w.under (𝓞 (maximalRealSubfield L))} y := by
    intro v hv
    refine Matrix.ext fun i j => ?_
    have h0 := hc v (y.1.val i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) fun u hu => by
      have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
        (fun e => hv (hu.symm.trans e)))
      have h1 := F.loc y u i j
      rw [hy, h] at h1
      rw [map_sub]
      change F.κ _ u - F.κ _ u = 0
      rw [← h1]
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs <;> simp <;> rfl
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hy0 : y ∈ U0 := (hU0 y hyt).2 hyU
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hU.aut _ (U.sub_mem (hU.stable _ _ hφU) hφU)) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  change φ (F.j g * x.val) - φ (F.j g) = 0
  rw [← hy, ← map_mul, sub_eq_zero]
  exact hfix g y hy0

end GlobalTheory.UnramDict

end
