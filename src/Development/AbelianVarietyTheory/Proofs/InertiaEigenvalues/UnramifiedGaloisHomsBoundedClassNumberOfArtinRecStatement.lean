module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRec
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ReciprocityTheory.ChartRestriction.T2.VhE := by
  first | exact @GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | exact GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | (intros; apply GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity <;> assumption)
