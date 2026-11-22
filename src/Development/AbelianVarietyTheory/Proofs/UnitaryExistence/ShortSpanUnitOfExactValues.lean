module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ShortRuleRepresentationChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.NormFactorThetaValue
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdmissibleFalseIffFirstInvariant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricLiftsOfFrames
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortSpanCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism hiding IsShortRule shortGen ShortInCusp
open GlobalTheory.GenusLatCompare GlobalTheory.LevelCoverCompare GlobalTheory.ShortDatumEq GlobalTheory.TransferCompare

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

section Generators

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

theorem evR_of_frMap {f : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf : f ∈ sec Xo c a n) {p : TRing c.F}
    {S : Type} [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) {y : FrPt Xo c p.R} {z : FrPt Xo c S}
    (h : FrMap φ y z) : evR Xo c f z = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact evalWD_framed Xo c f hf.1 S _ _ _ _ _ _ z hT.choose_spec.choose_spec.choose_spec h

variable {Δ}

end Generators

section Spans

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)

variable {Δ}

end Spans

section Claims

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)
  (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))

variable {Δ hK nV}

end Claims

section Std

variable (Xo c) (nab : NabV Xo c)

variable {Xo c nab}

variable (Xo c nab)

variable {Xo c nab}

end Std

end GlobalTheory.ShortSpanCompare
