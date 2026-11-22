module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_cohomology_nerve_homology_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveCx.obj (toMod F)).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveCx.obj (toMod F)).homology (n + 1)) :=
  @GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx
