module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExistsStatement

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.CuspFinGL

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (GlobalTheory.CompanionTheory.GGPS.ggps_bound E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (GlobalTheory.T.arch_lie_derivative_exists E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

end GlobalTheory.CompanionTheory.CuspFinGL
