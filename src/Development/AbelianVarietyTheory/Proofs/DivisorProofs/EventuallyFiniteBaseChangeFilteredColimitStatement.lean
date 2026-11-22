module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff

@[expose] public section

open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_finite_baseChange_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      (letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
        Module.Finite (F.obj k) (F.obj k ⊗[F.obj j] A)) := by
  exact @GlobalTheory.FiniteColim.eventually_finite_baseChange
