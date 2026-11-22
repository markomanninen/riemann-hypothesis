module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBaseStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndexStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscrStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilateStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInvStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacterStatement

@[expose] public section

namespace GlobalTheory.Proof.cm_localDensities_productFormula

theorem densityProduct : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct :=
  fun F E _ _ _ _ _ _ σ h₁ h₂ h₃ =>
    ⟨GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base F E σ h₁ h₂ h₃, GlobalTheory.T.dual_lattice_different_index F E σ h₁ h₂ h₃, GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr F E σ h₁ h₂ h₃,
      GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate F E σ h₁ h₂ h₃, GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv F E σ h₁ h₂ h₃, GlobalTheory.T.product_localDensities_adeleCharacter F E σ h₁ h₂ h₃⟩

end GlobalTheory.Proof.cm_localDensities_productFormula
