module

public import ReciprocityTheory.Hypotheses.GalCoh
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixingStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomologyStatement
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutside
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.FiniteH2TorsionModule

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem NS_eq_fixingSubgroup (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
  le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (GlobalTheory.T.galois_unramified_outside_cohomology F Ω S)

end GlobalTheory.CompanionTheory.Hypotheses₂
