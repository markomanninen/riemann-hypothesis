module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
public import GroundTheory.GlobalFields.TateThesis.TraceLatticePoisson
public import GroundTheory.GlobalFields.TateThesis.AdelePoisson

@[expose] public section

noncomputable section

open NumberField NumberField.mixedEmbedding
open scoped Classical

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def toR : mixedSpace F →ₗ[ℝ] UpperTheory.V.TR.Rinf F where
  toFun x v := x.1 ⟨v, IsTotallyReal.isReal v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
