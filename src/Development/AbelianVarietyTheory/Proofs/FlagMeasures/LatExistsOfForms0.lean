module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LatExistsOfSteps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveVectorNormNegHyperbolicPairStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsotropicOrthHyp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver

@[expose] public section

open Formalism.BasicNotions Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St.Lat

theorem latExists_of_forms0 : ∀ D : D7, Formalism.L2.Forms.Forms0 D D.u₀ → LatExists D := by
  intro D hF
  refine GlobalTheory.St.Lat.latExists_of ?_ ?_ D ?_
  · exact GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair
  · exact GlobalTheory.unramified_degree_one_of_ncard_placesOver
  · exact GlobalTheory.IsoOrthHyp.exists_isotropic_orth_hyp D hF

end GlobalTheory.St.Lat
