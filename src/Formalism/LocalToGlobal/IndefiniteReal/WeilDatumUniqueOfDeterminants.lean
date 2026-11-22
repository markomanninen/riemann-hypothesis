module

public import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

def DeterminantInUnitaryOne : Prop :=
  ∀ (D : D7) (V : HSp D) (g : GA D V), (mt V g).det * cA D (mt V g).det = 1

def SplitDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) * cA D (x : AE D) = 1 →
    SuppAtU D e x → ∃ g : GA D V, SuppAt e V g ∧ (∃ x', IsDetAt e V g x') ∧ (mt V g).det = x

variable {D : D7}

theorem mt_one' (V : HSp D) : L2.Theta.mt V 1 = 1 := by
  simp [L2.Theta.mt, map_one]

section Scalar

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W))

end Scalar

section Side

end Side

end Formalism.IndefR.flipTwoThree

end
