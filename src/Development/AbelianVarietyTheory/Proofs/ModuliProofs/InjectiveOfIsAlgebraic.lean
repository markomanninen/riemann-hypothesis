module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TateUniformizationInput
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfPowEqInt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcInputCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt

attribute [local instance] gtGroup

section Classes

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

variable (hB : D.TauBimult) (oa : D.OAct O) (F : Type) [Field F] [Algebra (FractionRing R) F]

variable {F} {k : ℕ}

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem isRatio_ext {p p' : QkPt D F k} {z : F} (h : QkPairing.IsRatio p p' z) :
    QkPairing.IsRatio (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  intro T σ y J hJ
  have e := h T (σ ≫ extMap f hf) y J hJ
  have v : ∀ (g : GtPtF D F) χ, val ((gtExt D f hf g).s χ) σ.left y J = val (g.s χ) (σ ≫ extMap f hf).left y J :=
    fun g χ => (val_corr hJ (((eq_gtExt_iff f hf g _).1 rfl).2 χ) _).trans (val_pull hJ _ _ _)
  have w : gs σ.left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (f z)) =
      gs (σ ≫ extMap f hf).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
    refine Eq.trans (congrArg (gs σ.left y ⊤) ?_) (gs_pull σ.left (spMap f) y ⊤ trivial _)
    exact congrArg (fun g => g.hom z) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  dsimp only [qkExt, qkMk]
  rw [v, v, w, gtExt_b, gtExt_b, ← Category.assoc, ← Category.assoc]
  exact e

theorem weil_ext (k : ℕ) (hk : 1 ≤ k) (p p' : QkPt D F k) (z : F) (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F' k (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  obtain ⟨u, hu⟩ := QkPairing.exists_ratio p p'
  obtain rfl := QkPairing.weil_unique globalFns_holds abelianSchemeLaws_all.2.secTwist hB hk p p' h
    (QkPairing.weil_of_ratio globalFns_holds p p' hu)
  exact QkPairing.weil_of_ratio globalFns_holds _ _ (ζ := Units.map f.toMonoidHom u) (isRatio_ext hB f hf hu)

end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Data

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]


variable (hB : P.TauBimult)


end Data

section Lev

variable (D : Datum H) (l : Level H)

end Lev

section Level

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {l : Level H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (hB : P.TauBimult)


variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')


end Level

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}


end ThetaShiftProofs

section Main

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

end Main

end GlobalTheory.ArcInputCompare
