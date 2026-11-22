module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicQuotientMeasure
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

@[expose] public section

noncomputable section

open MeasureTheory NumberField GlobalTheory.IndefiniteRowSideFullHecke.AdelicQuotientClasses
open scoped ENNReal NNReal Pointwise Classical

namespace GlobalTheory.AutQuotCompare

section First

variable {H : Type} [Group H] (Γ : Subgroup H)

variable [MeasurableSpace H] (P P' : Measure H × Set H → Prop)

end First

section Haar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

end Haar

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

variable {G}

end Adelic

section Transport

variable {H H' : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H']
  {Γ : Subgroup H} {Γ' : Subgroup H'} (e : H ≃ₜ* H') (he : ∀ g, e g ∈ Γ' ↔ g ∈ Γ)


variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H']

end Transport

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {G : Matrix (Fin n) (Fin n) E}
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  {Γ : Subgroup H}

def IsHaarPair (Γ : Subgroup H) (p : Measure H × Set H) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain Γ p.2 p.1

end Main

section Split

open scoped Matrix

variable {R S ι : Type} [CommRing R] [CommRing S] (Φ : R ≃+* (ι → ℂ) × S) {n : ℕ}

def compAt (w : ι) : R →+* ℂ := (Pi.evalRingHom _ w).comp ((RingHom.fst _ _).comp Φ.toRingHom)

def compLast : R →+* S := (RingHom.snd _ _).comp Φ.toRingHom

theorem continuous_map {R R' : Type} [CommRing R] [CommRing R'] [TopologicalSpace R] [TopologicalSpace R']
    {φ : R →+* R'} (h : Continuous φ) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) φ) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map h, Units.continuous_coe_inv.matrix_map h⟩

variable [TopologicalSpace R] [TopologicalSpace S] (hc : Continuous Φ) (hc' : Continuous Φ.symm)
  {s : R →+* R} {s' : S →+* S} (hs : ∀ w z, compAt Φ w (s z) = starRingEnd ℂ (compAt Φ w z))
  (hs' : ∀ z, compLast Φ (s z) = s' (compLast Φ z)) {J : Matrix (Fin n) (Fin n) R}
  {A : ι → Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) S}
  (hA : ∀ w, Jᵀ.map (compAt Φ w) = A w) (hB : Jᵀ.map (compLast Φ) = B)

end Split

section Adeles

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem sigmaCompact_inf (F : Type) [Field F] [NumberField F] [Algebra F E] : SigmaCompactSpace (Ainf F ⊗[F] E) := by
  have : ∀ v : InfinitePlace F, SigmaCompactSpace v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.sigmaCompactSpace
  have : SigmaCompactSpace (Ainf F) := inferInstanceAs (SigmaCompactSpace (∀ v : InfinitePlace F, v.Completion))
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (Ainf F) (Ainf F ⊗[F] E)
  refine ⟨?_⟩
  rw [← hf.range_eq]
  exact isSigmaCompact_range (IsModuleTopology.continuous_of_linearMap f)

theorem exists_inf_equiv : ∃ Θ : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E ≃+* (InfinitePlace E → ℂ),
    Continuous Θ ∧ Continuous Θ.symm ∧ (∀ x w, Θ (1 ⊗ₜ x) w = w.embedding x) ∧
      ∀ z w, Θ (GlobalTheory.AdLat.sg _ (IsCMField.complexConj E) z) w = starRingEnd ℂ (Θ z w) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective (maximalRealSubfield E) E (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) inferInstance
    (IsCMField.complexEmbedding_complexConj E)
  choose θ hθ using h1
  obtain ⟨h3, h4, h5⟩ := h2 θ hθ
  have hinj : Function.Injective (fun w : InfinitePlace E => w.embedding) := fun v w h => by
    rw [← v.mk_embedding, ← w.mk_embedding]; exact congrArg _ h
  have hmem : ∀ τ : E →+* ℂ, τ ∈ Set.range (fun w : InfinitePlace E => w.embedding) ↔
      (InfinitePlace.mk τ).embedding = τ := fun τ =>
    ⟨fun ⟨w, hw⟩ => by rw [← hw]; simp only [InfinitePlace.mk_embedding], fun h => ⟨_, h⟩⟩
  have hb := h5 (Set.range fun w : InfinitePlace E => w.embedding) fun τ => by
    have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
      IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
    rw [hmem, hmem, InfinitePlace.mk_conjugate_eq]
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]; simp [hne.symm]
    · rw [h]; simp [hne]
  let f : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* (InfinitePlace E → ℂ) :=
    Pi.ringHom fun w => θ w.embedding
  have hf : Function.Bijective f :=
    (Equiv.arrowCongr (Equiv.ofInjective _ hinj).symm (Equiv.refl ℂ)).bijective.comp hb
  have hfc : Continuous f := continuous_pi fun w => h3 _
  have := sigmaCompact_inf E (maximalRealSubfield E)
  have : IsModuleTopology (Ainf (maximalRealSubfield E))
    (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) := ⟨rfl⟩
  have : IsTopologicalRing (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
    IsModuleTopology.isTopologicalRing (Ainf (maximalRealSubfield E)) _
  have ho : IsOpenMap f := f.toAddMonoidHom.isOpenMap_of_sigmaCompact hf.2 hfc
  refine ⟨RingEquiv.ofBijective f hf, hfc, ?_, fun x w => (hθ _).1 x, fun z w => h4 _ z⟩
  exact ((RingEquiv.ofBijective f hf).toEquiv.toHomeomorphOfContinuousOpen hfc ho).symm.continuous

end Adeles

section Groups

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Groups

section Record

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} [IsCMField D.host.E] (V : HSp D)

omit [IsCMField D.host.E]

end Record

end GlobalTheory.AutQuotCompare
