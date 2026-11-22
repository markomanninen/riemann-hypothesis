module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandra
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLiftIsotropicSubspaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

theorem inputs_of_chosenSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
      GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (X : ProvA), ChosenSeries X → Inputs D X := by
  intro hDS hHC hDec hCW D X hX
  exact
    { chosen := hX
      hc := hHC
      decay := hDec
      bridge := GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D
      vacChar := GlobalTheory.VacuumCharacter.vacChar D
      lie := GlobalTheory.LieScalar.lieFockAll D
      cpt := GlobalTheory.CompactFockAction.compactFockAll D
      dense := GlobalTheory.FockDensity.fockDense D
      laws := GlobalTheory.Chain.LiftReg.liftProps_obj hDec D
      const := GlobalTheory.T.constantTermLift_isotropicSubspace D
      ext := GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors hHC hCW D }

end GlobalTheory.PairLift
