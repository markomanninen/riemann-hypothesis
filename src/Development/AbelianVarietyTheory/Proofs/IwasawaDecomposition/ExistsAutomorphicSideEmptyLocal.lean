module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeParametersInertPlaceIndependentOfModelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitoneStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordinateModelOfAlgWeightStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicRepCmQuotientModelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicMultiplicityEqOfIsoStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentConjSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SphericalVectorFixedLocal

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem autIso_symm {π π' : NG.AutRep L n} (h : π.Iso π') : π'.Iso π := (NG.AutRep.iso_equivalence (L := L) (n := n)).symm h

theorem autIso_trans {π π' π'' : NG.AutRep L n} (h : π.Iso π') (h' : π'.Iso π'') : π.Iso π'' :=
  (NG.AutRep.iso_equivalence (L := L) (n := n)).trans h h'

theorem clsA_eq_iff (π π' : NG.AutRep L n) : clsA π = clsA π' ↔ π.Iso π' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := GlobalTheory.T.automorphic_rep_cm_quotient_model L n π'
    have h2 : m ∈ (clsA π).1 := by rw [h]; exact hm
    exact autIso_trans h2 (autIso_symm hm)
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => autIso_trans (autIso_symm h) h', fun h' => autIso_trans h h'⟩

theorem clsW_eq_iff (a b : NG.AlgWt L n) : clsW a = clsW b ↔ a.Iso b := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_coordinate_model_of_algWeight L n b
    have h2 : m ∈ (clsW a).1 := by rw [h]; exact hm
    exact h2.trans hm.symm
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem rep_iso (π : NG.AutRep L n) : (clsA π).rep.Iso π :=
  (clsA_eq_iff _ _).1 (AUq.cls_rep (clsA π))

theorem repW_iso (a : NG.AlgWt L n) : (clsW a).rep.Iso a :=
  (clsW_eq_iff _ _).1 (WtQ.cls_rep (clsW a))

theorem sphAt_iso {π π' : NG.AutRep L n} (h : π.Iso π') {v} (hs : π.SphAt v) : π'.SphAt v := by
  obtain ⟨-, T, hT⟩ := h
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  refine ⟨(T ⟨f, hf⟩ : _), (T ⟨f, hf⟩).2, ?_, fun κ hκ ht => ?_⟩
  · intro h0
    apply hf0
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val (T.injective (this.trans T.map_zero.symm))
    exact this
  · have := hT κ ⟨f, hf⟩ ⟨f, hf⟩ (hfix κ hκ ht).symm
    exact this.symm

omit [NumberField L] [IsCMField L] in
theorem overPl_unique {w : HeightOneSpectrum (𝓞 L)} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (h : NG.OverPl w v) (h' : NG.OverPl w v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem locAt_of_split (π : NG.AutRep L n) (s : SplitPlace L) : ∃ x, LocAt π s.w x := by
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  exact ⟨_, s, σ, rfl, hσ, HEq.rfl⟩

theorem locAt_unique {π π' : NG.AutRep L n} (hi : π.Iso π') {w : HeightOneSpectrum (𝓞 L)} {x x'}
    (hx : LocAt π w x) (hx' : LocAt π' w x') : x = x' := by
  obtain ⟨s, σ, hs, hσ, e⟩ := hx
  obtain ⟨s', σ', hs', hσ', e'⟩ := hx'
  obtain ⟨σ₀, -, hu⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  have h1 := hu π s rfl σ ((NG.AutRep.iso_equivalence (L := L) (n := n)).refl π) hσ
  have h2 := hu π' s' (hs'.trans hs.symm) σ' hi hσ'
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 L)) (_ : u = u') (a : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u.adicCompletion L)))
      (b : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u'.adicCompletion L))), HEq a b →
      HEq (⟨n, a⟩ : GlobalTheory.LocGL.IrrGL (k := u.adicCompletion L)) (⟨n, b⟩ : GlobalTheory.LocGL.IrrGL (k := u'.adicCompletion L)) := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    rfl
  have h3 : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls σ') :=
    key _ _ (hs.trans hs'.symm) _ _ (h1.trans h2.symm)
  exact eq_of_heq (e.symm.trans (h3.trans e'))

end

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable (D : D7)

theorem f_sat (π : NG.AutRep D.host.E D.R.nV) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (w : PlE D.host)
    (hv : NG.OverPl w v) (Dv : InertDatum D.host.E D.R.nV v w) (hα : ∃ α, NG.SatAt π Dv α) :
    ∃ α, NG.SatAt π Dv α ∧ satOf (clsA π).rep w = Finset.univ.val.map α := by
  obtain ⟨α, hα⟩ := hα
  have hex : ∃ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' ∧ NG.SatAt (clsA π).rep Dv' α' :=
    ⟨v, Dv, α, hv, GlobalTheory.T.satakeParameters_inertPlace_independent_of_model _ _ π _ (autIso_symm (rep_iso π)) v w hv Dv Dv α hα⟩
  unfold satOf
  rw [dite_eq_left hex]
  have key : ∀ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' → NG.SatAt (clsA π).rep Dv' α' → NG.SatAt π Dv α' := by
    intro v' Dv' α' hv' hs'
    have e := overPl_unique hv hv'
    subst e
    exact GlobalTheory.T.satakeParameters_inertPlace_independent_of_model _ _ _ π (rep_iso π) v w hv _ Dv _ hs'
  obtain ⟨hv', hs'⟩ := hex.choose_spec.choose_spec.choose_spec
  exact ⟨_, key _ _ _ hv' hs', rfl⟩

theorem f_wt (π : NG.AutRep D.host.E D.R.nV) (a : NG.AlgWt D.host.E D.R.nV) (hd : π.toAlgWt.IsDual a) :
    wtOf D (clsA π).rep = clsW a := by
  have hπ : (clsA π).rep.toAlgWt.Iso π.toAlgWt := (rep_iso π).1
  obtain ⟨b, hb, hbu, hba⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ π.toAlgWt
  have hrb : (clsA π).rep.toAlgWt.IsDual b := (hba _ hπ.symm).1
  have hex : ∃ b, (clsA π).rep.toAlgWt.IsDual b := ⟨b, hrb⟩
  unfold wtOf
  rw [dite_eq_left hex]
  obtain ⟨b', -, hbu', -⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ (clsA π).rep.toAlgWt
  have h1 : b'.Iso hex.choose := (hbu' _).1 hex.choose_spec
  have h2 : b'.Iso b := (hbu' _).1 hrb
  have h3 : b.Iso a := (hbu a).1 hd
  exact (clsW_eq_iff _ _).2 ((h1.symm.trans h2).trans h3)

theorem f_infW (a : NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ) (hl : a.HWAt τ lam) :
    NG.infOf (hwOf (clsW a).rep τ) = NG.infOf lam := by
  have hi : a.Iso (clsW a).rep := (repW_iso a).symm
  obtain ⟨b0, hb0, hb0', hhw⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ a
  have hr : (clsW a).rep.HWAt τ lam := ((hhw _ hi).2 τ lam hl)
  obtain ⟨huniq, hanti⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ (clsW a).rep τ
  have hex : ∃ lam, (clsW a).rep.HWAt τ lam ∧ Antitone lam := ⟨lam, hr, hanti lam hr⟩
  unfold hwOf
  rw [dite_eq_left hex, huniq.unique hex.choose_spec.1 hr]

end

end GlobalTheory.AutQuot
