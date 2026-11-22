module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExistsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRamifiedOfRamifiedLocalComponentStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldPlaceInRamifiedSetStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsotyStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfUpperParahoricEigenStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProductStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockTypeVectorIrreducibleSplitsAsProductStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypesAtPin

theorem not_over_g_of_mem_Q (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ D.nd.Q i)
    (k : Fin 2) : w ∉ placesOver D.host.E (D.host.g k) := by
  intro hk
  have hS : w ∈ D.nd.S i := (D.nd.S_def i w).2 ⟨by
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk), D.nd.SQ_l i w (Or.inr hw)⟩
  exact Finset.disjoint_left.1 (D.nd.SQ_disj i) hS hw

end GlobalTheory.TypesAtPin
