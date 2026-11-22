module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaValueNaturalField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMoveBack
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansions
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePullExpands
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamily
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GeneratorsCompare

open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

section Trans

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing V) F]

variable {F}

end Trans

section PEL

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
  [CharZero V] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem torsionIso {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t) : P.TorsionIso := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.lawsAndExpansions
  exact GlobalTheory.UT.torsionIso_of_pelUnif h₁ h₂ h₃ h₄ h₅ E H _ _
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t P

end PEL

section Concl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

variable (nab : NabV Xo c) (y) (F : Type) [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ)) (ν : c.F)
  (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (val : MvPolynomial (LtN Dw n) c.F → F)

variable {nab y F v ν a val}

end Concl

section Germs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ) {n : ℕ}
  {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)} [GrpObj G']
  [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} {pG : IsPowGrp G' C.I.G.G n}
  {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
  (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ))

end Germs

end GlobalTheory.GeneratorsCompare
