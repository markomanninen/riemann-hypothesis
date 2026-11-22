module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Norms

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]

end Norms

def WaveUniq : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → (∀ g ∈ GLs n, u 0 g = v 0 g) →
    ∀ t, ∀ x ∈ GLs n, u t x = v t x

end GlobalTheory.CompanionTheory.WaveK
