module

public import Mathlib
public import Formalism.PeriodIntegrals.OmFibreUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreUniqueness
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.AdditiveCharacterNontrivial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExInst

@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem omUnique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : ℕ) :
    PI.OmFibreUniq.OmUnique σ J ψ v a :=
  PI.OmFibreUniq.W.omUnique_of_sdEx
    (PI.OmFibreUniq.W.SdInst.sdEx_of_psiNT PI.OmFibreUniq.W.Sd.additive_character_nontrivial) σ J ψ v a
