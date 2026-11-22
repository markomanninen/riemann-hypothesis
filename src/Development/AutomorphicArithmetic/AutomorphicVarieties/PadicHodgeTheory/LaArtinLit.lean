module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

theorem UpperTheory.V.Loc.localArtinReciprocity (H : GlobalTheory.Mem.LiteralAutomorphy.LitN) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) :
    ∃ a, IsLocalArtin h a := by
  obtain ⟨rc, hrc⟩ := H.loc.llc F Ω A w h
  obtain ⟨a, ha, -⟩ := hrc
  exact ⟨a, ha⟩
