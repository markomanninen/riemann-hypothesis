module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbedding
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_btOrder_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top | exact GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top <;> assumption)
