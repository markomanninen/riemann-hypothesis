module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_order_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | exact GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | (intros; apply GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one <;> assumption)
