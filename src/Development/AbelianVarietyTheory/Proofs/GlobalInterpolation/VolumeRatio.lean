module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatioOfUnfolding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeDensity
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealPlaceMeasures
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EulerProductOfDensities
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolIndep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Unfolding

@[expose] public section

namespace GlobalTheory.VolRatioFromSecondClause

theorem volumeRatio : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1b2 F E σ M J) → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D :=
  fun hSW D =>
    GlobalTheory.VolRatioUnfold.volumeRatio_of_unfolding GlobalTheory.LatticeDensityClosed.selfDualLatticeDensity
      GlobalTheory.RealPlaceMeasuresProof.realPlaceMeasures GlobalTheory.DensityProductClosed.eulerProductOfDensities
      GlobalTheory.VolIndepClosed.volIndep GlobalTheory.UnitPerpObj.unitVectorPerp GlobalTheory.UnfoldingObj.unfolding hSW D

end GlobalTheory.VolRatioFromSecondClause
