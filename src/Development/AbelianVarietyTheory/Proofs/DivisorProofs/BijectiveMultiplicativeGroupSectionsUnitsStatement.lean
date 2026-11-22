module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_multiplicativeGroup_sections_units :
    ∀ U : Scheme.{0}, Function.Bijective (ofRings.sec unitsF U) := by
  have hGamma : Presheaf.IsSheaf Scheme.etaleTopology.{0} Scheme.Γ := by
    intro R
    have gammaIso : Scheme.Γ ⋙ coyoneda.obj (op R) ≅ yoneda.obj (Spec R) :=
      NatIso.ofComponents
        (fun U => (Equiv.trans (Quiver.Hom.opEquiv)
          (ΓSpec.adjunction.homEquiv U.unop (op R))).toIso)
        (by
          intro U V f
          ext g
          exact ΓSpec.adjunction.homEquiv_naturality_left f.unop g.op)
    exact Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (Presieve.isSheaf_iso _ gammaIso.symm
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
  have hUnits : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ unitsF) := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
    let F := forget₂ CommRingCat.{0} CommMonCat ⋙ CommMonCat.units ⋙
      forget CommGrpCat ⋙ uliftFunctor.{1, 0}
    have hF : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ F) :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ F hGamma
    exact hF
  intro U
  have := isIso_toSheafify Scheme.etaleTopology hUnits
  delta ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U))
