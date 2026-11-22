module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnity
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
theorem _root_.GlobalTheory.T.exists_isOpen_subgroup_adicUnits_no_rootsOfUnity : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ V : Subgroup (w.adicCompletion E)ˣ,
    IsOpen (V : Set (w.adicCompletion E)ˣ) ∧ ∀ t : Eˣ, (∃ n : ℕ, 0 < n ∧ t ^ n = 1) →
      Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom t ∈ V → t = 1 := by
  first | exact @GlobalTheory.RootOpen.exists_open_subgroup_no_roots | exact GlobalTheory.RootOpen.exists_open_subgroup_no_roots | (intros; apply GlobalTheory.RootOpen.exists_open_subgroup_no_roots <;> assumption)
