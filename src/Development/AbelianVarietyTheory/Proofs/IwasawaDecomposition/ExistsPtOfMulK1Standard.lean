module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh.KStd

theorem K1_le_J0_empty {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) :
    K1 B.sp.cm n ST SG ≤ J0 B.sp.cm n ∅ := by
  intro t ht
  have h1 := principal_le_congruence_subgroup B.sp.cm n ST SG ht
  unfold J0 at h1 ⊢
  simp only [Subgroup.mem_inf] at h1 ⊢
  refine ⟨h1.1, ?_⟩
  simp

theorem exists_ptOf_mul_K1 : ∀ {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) (k t : GA B n), t ∈ K1 B.sp.cm n ST SG → (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) → ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  intro B n _ ST SG k t ht ⟨p, hp, hN⟩
  have hz : t ∈ J0 B.sp.cm n ∅ := K1_le_J0_empty n ST SG ht
  refine ⟨p, ?_, hN⟩
  refine (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw B.host.F B.host.E B.sp.cm n ∅ ∅ ∅ (k * t) p rfl).2 ⟨?_, ?_⟩
  · exact mul_mem hp.uni (congruence_le_adelic_unitary B.sp.cm n ∅ hz)
  · have h := decoRaw_rawSm B.sp.cm ∅ ∅ 1 (⟨t, hz⟩⁻¹ : J0 B.sp.cm n ∅) k
    rw [map_one, map_inv] at h
    have e : Formalism.UG.bc (iA B.host.F B.host.E) ((1 : URat B.sp.cm n) : GL (Fin n) B.host.E) * k *
        (((⟨t, hz⟩⁻¹ : J0 B.sp.cm n ∅) : J0 B.sp.cm n ∅) : GL (Fin n) (AfE B.host.F B.host.E))⁻¹ = k * t := by
      simp
    rw [e] at h
    have hr : (redG B.sp.cm n ∅ ∅ ⟨t, hz⟩)⁻¹ = 1 := Subsingleton.elim _ _
    rw [hr] at h
    rw [(near_of_isPtOf hp 0).deco] at h
    simp only [map_one] at h
    change decoRaw ∅ ∅ (k * t) = Deco.act 1 1 p.deco.1 at h
    rw [Deco.act_one] at h
    exact h.symm

end GlobalTheory.Mem.Col2.TopCh.KStd

end
