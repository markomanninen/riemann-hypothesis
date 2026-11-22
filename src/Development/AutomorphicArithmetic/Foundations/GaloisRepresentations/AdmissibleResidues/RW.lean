module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WitApi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealDefs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def RW (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    ∀ s : G F Ω, IsFrob A (normV w) s → ∀ α β : Qbar l, (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot α →
      (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot β → ‖ι α‖ < ((normV w : ℕ) : ℝ) * ‖ι β‖

end UpperTheory.GalN.V
