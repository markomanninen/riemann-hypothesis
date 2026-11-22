module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBelowCMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceBelowCMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w := by
  first | exact @GlobalTheory.SplitPlaceExists.exists_isSplitAt | exact GlobalTheory.SplitPlaceExists.exists_isSplitAt | (intros; apply GlobalTheory.SplitPlaceExists.exists_isSplitAt <;> assumption)
