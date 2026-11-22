module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoVanEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLineZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLineNeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.hostVanE : ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → LocalFiniteness → LocalTateDuality → LocalEulerChar → UnitaryThreeInertia.HostVanE := by
  intro CK hK hPT hLFK hLTDK hLF hLTD hLEC Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF
  apply So.vanEOf c.O _ _ _ F
  intro j hj s
  rcases hj.lt_or_eq with hlt | heq
  · exact So.lineNeg CK hK hPT hLFK hLTDK hLF hLTD hLEC Ω l c N e ψ S A F hD.e_pos hF j hlt s
  · subst heq
    exact So.lineZero c.O _ _ _ F (UnitaryThreeInertia.frame_class_one Ω c e ψ o₁ hD S A F hF) s
