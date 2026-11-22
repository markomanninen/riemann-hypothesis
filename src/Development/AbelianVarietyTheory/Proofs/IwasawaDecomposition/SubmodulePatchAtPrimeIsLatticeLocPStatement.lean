module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmodulePatchAtPrimeIsLatticeLocP
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf

@[expose] public section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodulePatchAtPrime_isLattice_locP : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsFullLattice E A → Submodule.IsFullLattice E B → Submodule.IsLattice E (patchAt P A B) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (patchAt P A B) = localization₂ Q.asIdeal (if Q = P then A else B) := by
  intro E _ _ _ n P A B hA hB
  first
  | exact GlobalTheory.InertExchange.patchAt_isLattice_locP P A B hA hB
  | exact GlobalTheory.InertExchange.patchAt_isLattice_locP P A B hA.toIsLattice hB.toIsLattice
