module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem exists_locTheory_tied : ∃ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
    Nonempty (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) := by
  choose P A h using exists_locPrime_tied
  exact ⟨fun l _ => P l, fun l _ => A l, ⟨fun l _ => (h l).some⟩⟩
end GlobalTheory.MemLoc
