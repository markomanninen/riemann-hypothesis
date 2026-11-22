module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBaseStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRingStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polBaseChange_holds : PolBaseChangeSt :=
  polBaseChange_of_relAmple_local T.relAmple_of_locally_on_base

theorem cubical_extends_holds : Semi.cubical_extendsSt.{0} :=
  (cubical_extends_and_extendGen
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected T.existsUnique_generator_extend_discreteValuationRing).1

theorem laws_without_cohomology :
    GlobalFnsSt ∧ RigiditySt ∧ PolBaseChangeSt ∧ Semi.lemmaBSt.{0} ∧ Semi.cubical_extendsSt.{0} :=
  ⟨globalFns_holds, rigidity_holds, polBaseChange_holds, lemmaB_holds, cubical_extends_holds⟩

end GlobalTheory
