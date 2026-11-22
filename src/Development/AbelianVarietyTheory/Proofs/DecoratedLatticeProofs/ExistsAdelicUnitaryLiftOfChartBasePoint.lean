module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameOnBaseCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmooth
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.BasePointLift

theorem exists_lift_of_ptOf : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) (k : TC.GA B (B.R.N i)), (∃ p : Formalism.L2.Col.DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, TC.PtOf k p ∧ p.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) → ∃ kA : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i), kA ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) kA = k.1 := by
  intro B X I hI hP l Z i hi k hk
  obtain ⟨p, hp, -⟩ := hk
  have hu := hp.uni
  obtain ⟨-, -, -, hg⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  have hg1 := (hg i hi).1
  unfold Formalism.L2.Forms.gramN at hg1
  have hy : k ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))
      (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).gram.reindex (finCongr (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi)) (finCongr (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi)))
      (FiniteAdeleRing (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := by
    rw [hg1]
    change k ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i)
    exact hu
  obtain ⟨a, ha, e⟩ := GlobalTheory.Core.Mi.PinModel.exists_finM _ (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi) ⟨k, hy⟩
  exact ⟨a, ha, e⟩

end GlobalTheory.BasePointLift

end
