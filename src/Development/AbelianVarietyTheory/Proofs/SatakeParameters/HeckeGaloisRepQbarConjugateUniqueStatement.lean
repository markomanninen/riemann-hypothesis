module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisRepQbarConjugateUnique
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.RepConjUniq.main | exact GlobalTheory.RepConjUniq.main | (intros; apply GlobalTheory.RepConjUniq.main <;> assumption)
