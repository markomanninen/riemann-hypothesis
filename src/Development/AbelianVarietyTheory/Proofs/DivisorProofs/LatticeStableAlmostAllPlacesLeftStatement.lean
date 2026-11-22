module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → ∀ M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  exact @GlobalTheory.AdelMatLat.almost_all_stable
