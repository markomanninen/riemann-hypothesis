module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLatticeConditionOfSeriesComparisonUniversal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalTwistedSeriesDistributionOfCompatibilitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricPropertiesAllOfBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsToricEltOfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullDegreeLabelForcesTrivialWildInertiaStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLawsOfSides
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LawsOfSerSide
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfSides
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnivSupOfXi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiType

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem levelOf_of_serSide {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b g => (Y.Z.tie i j b).U_eq g, fun i j b u hu => (Y.Z.tie i j b).psiU_eq u hu⟩

end GlobalTheory.TwInputs
