module

public import Mathlib

@[expose] public section

open scoped TensorProduct NumberField
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarMultiplier

abbrev Af : Type := FiniteAdeleRing ℤ ℚ

def zHat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum ℤ, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers ℚ)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers ℚ)
  neg_mem' ha v := neg_mem (ha v)

def zHatUnits : Subgroup Afˣ := zHat.toSubmonoid.units

abbrev Idele (K : Type) [Field K] [NumberField K] : Type := (Af ⊗[ℚ] K)ˣ

def ideleNorm (K : Type) [Field K] [NumberField K] : Idele K →* Afˣ :=
  Units.map (Algebra.norm Af : Af ⊗[ℚ] K →* Af)

def NormUnitCond {K : Type} [Field K] [NumberField K] (s : Idele K) (q : ℚ) : Prop :=
  ∃ u ∈ zHatUnits, (u : Af) = (((ideleNorm K s)⁻¹ : Afˣ) : Af) * algebraMap ℚ Af q

section Herm

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W]



end Herm

section Groups

variable {E : Type} [Field E] [NumberField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]


variable [Module (𝓞 E) W]



end Groups

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarMultiplier
