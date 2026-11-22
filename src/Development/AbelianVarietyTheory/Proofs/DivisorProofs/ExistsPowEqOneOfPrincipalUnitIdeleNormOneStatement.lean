module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOne
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
theorem _root_.GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  first | exact @GlobalTheory.UnitTorsion.principal_unit_idele_torsion | exact GlobalTheory.UnitTorsion.principal_unit_idele_torsion | (intros; apply GlobalTheory.UnitTorsion.principal_unit_idele_torsion <;> assumption)
