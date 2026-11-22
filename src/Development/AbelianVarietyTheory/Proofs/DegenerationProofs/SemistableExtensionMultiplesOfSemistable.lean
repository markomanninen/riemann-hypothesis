module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NumberFieldStandardFacts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSection
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HenselianIUnionCompleteOfIntegralOverCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProjByBaseChange

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

theorem isAbelianScheme_overPullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) := by
  constructor
  · have := h.comm
    infer_instance
  · have := h.smooth
    change Smooth (pullback.snd A.hom f)
    infer_instance
  · have := h.proper
    change IsProper (pullback.snd A.hom f)
    infer_instance
  · have := h.geomConnected
    change GeometricallyConnected (pullback.snd A.hom f)
    infer_instance

end GlobalTheory
