module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

theorem descEt_of : DescEt := by
  intro A B C c f hc hs hf hcf
  exact GlobalTheory.etale_of_comp_of_etale_of_surjective c f

end UpperTheory.Gal.FixZ
