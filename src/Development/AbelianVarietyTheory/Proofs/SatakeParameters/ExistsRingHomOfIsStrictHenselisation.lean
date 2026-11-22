module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

noncomputable section
namespace GlobalTheory.NCyc.StrictLocLift

theorem lift_unique {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (g₁ g₂ : Q →+* T)
    (h₁ : g₁.comp tQ = b) (h₂ : g₂.comp tQ = b)
    (h : (residue T).comp g₁ = (residue T).comp g₂) : g₁ = g₂ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let G₁ : Q →ₐ[R] T := { g₁ with commutes' := fun r => DFunLike.congr_fun h₁ r }
  let G₂ : Q →ₐ[R] T := { g₂ with commutes' := fun r => DFunLike.congr_fun h₂ r }
  have := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).1 (a₁ := G₁) (a₂ := G₂) (by
    ext q; exact DFunLike.congr_fun h q)
  ext q; exact DFunLike.congr_fun this q

theorem lift_exists {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (ψ : Q →+* ResidueField T)
    (hψ : ψ.comp tQ = (residue T).comp b) :
    ∃ g : Q →+* T, g.comp tQ = b ∧ (residue T).comp g = ψ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let Ψ : Q →ₐ[R] ResidueField T := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  obtain ⟨G, hG⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).2 Ψ
  refine ⟨G.toRingHom, RingHom.ext fun r => G.commutes r, RingHom.ext fun q => ?_⟩
  exact DFunLike.congr_fun hG q

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isIndEtale {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [HenselianLocalRing T]
    (a : R →+* S) (b : R →+* T) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale a) (ψ : S →+* ResidueField T)
    (hψ : ψ.comp a = (residue T).comp b) : ∃ g : S →+* T, g.comp a = b := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := ha
  have hts' : ∀ j, (s.app j).hom.comp (t.app j).hom = a := fun j => by
    have := congrArg CommRingCat.Hom.hom (hts j).2
    simpa using this
  have hψj : ∀ j, (ψ.comp (s.app j).hom).comp (t.app j).hom = (residue T).comp b := fun j => by
    rw [RingHom.comp_assoc, hts' j, hψ]
  choose g hg using fun j => lift_exists (t.app j).hom (hts j).1 b (ψ.comp (s.app j).hom) (hψj j)
  have nat : ∀ {j k : J} (u : j ⟶ k), (g k).comp (D.map u).hom = g j := by
    intro j k u
    have ht : (D.map u).hom.comp (t.app j).hom = (t.app k).hom := by
      have := congrArg CommRingCat.Hom.hom (t.naturality u)
      simpa using this.symm
    have hs' : (s.app k).hom.comp (D.map u).hom = (s.app j).hom := by
      have e : D.map u ≫ s.app k = s.app j := by
        have := s.naturality u
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        exact this
      have := congrArg CommRingCat.Hom.hom e
      rwa [CommRingCat.hom_comp] at this
    apply lift_unique (t.app j).hom (hts j).1 b
    · rw [RingHom.comp_assoc, ht, (hg k).1]
    · exact (hg j).1
    · rw [← RingHom.comp_assoc, (hg k).2, RingHom.comp_assoc, hs', (hg j).2]
  let c : Cocone D :=
    { pt := CommRingCat.of T
      ι := { app := fun j => CommRingCat.ofHom (g j)
             naturality := fun j k u => by
               ext q
               simpa using DFunLike.congr_fun (nat u) q } }
  refine ⟨(hs.desc c).hom, ?_⟩
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  have hf : (hs.desc c).hom.comp (s.app j).hom = g j := by
    have := congrArg CommRingCat.Hom.hom (hs.fac c j)
    simpa [c] using this
  rw [← hts' j, ← RingHom.comp_assoc, hf, (hg j).1]

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isStrictHenselisation {R S T : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [CommRing T] [HenselianLocalRing T] [IsSepClosed (ResidueField T)]
    (a : R →+* S) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation a) (b : R →+* T) [IsLocalHom b] :
    ∃ g : S →+* T, g.comp a = b := by
  letI : Algebra R S := a.toAlgebra
  haveI : IsLocalHom (algebraMap R S) := ha.2.2.1
  obtain ⟨-, -, hsep⟩ := GlobalTheory.IndEtaleLocal.flat_map_maximalIdeal_isSeparable R S ha.2.2.2
  letI : Algebra (ResidueField R) (ResidueField T) := (ResidueField.map b).toAlgebra
  let ι : ResidueField S →ₐ[ResidueField R] ResidueField T := IsSepClosed.lift
  refine exists_ringHom_of_isIndEtale a b ha.2.2.2 (ι.toRingHom.comp (residue S)) (RingHom.ext fun r => ?_)
  have h1 : residue S (a r) = algebraMap (ResidueField R) (ResidueField S) (residue R r) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [h1, ι.commutes]
  rfl

end GlobalTheory.NCyc.StrictLocLift
