module

public import Mathlib
public import Formalism.LocalRingCardinality.DataLevel

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.L2.G.Triv

def IwProG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (v : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → (g : 𝓞 F) ∈ v.asIdeal →
    IsProGrp g (iwU F k v)

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

end Level

end Formalism.L2.G.Triv

end
