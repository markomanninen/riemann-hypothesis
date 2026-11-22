module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RGrowthPiJ
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.EigInert
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.NoAccum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.AllLeavesMono
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
open PositivityTheory.Rg.BcB.Desc
open PositivityTheory.Rg.BcB.F

namespace GlobalTheory.CompanionTheory.LFixDPf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}



section Conj

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

end Conj

section Int

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

theorem mem_KGL_map_conj (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    GeneralLinearGroup.map (conjLoc (conjE E) u) g ∈ GlobalTheory.LFun.KGL u (n := n) ↔ g ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) (n := n) := by
  have hv : ∀ x : (conjSrc (conjE E) u).adicCompletion E,
      conjLoc (conjE E) u x ∈ u.adicCompletionIntegers E ↔ x ∈ (conjSrc (conjE E) u).adicCompletionIntegers E := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec (conjE E) u).2.2 x]
  rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
  refine and_congr (forall₂_congr fun a b => hv _) (forall₂_congr fun a b => ?_)
  rw [← map_inv]
  exact hv _

end Int

section Int2

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

end Int2

section Main

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

variable {d : LocData E n}

end Main

section Core

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

end Core

end GlobalTheory.CompanionTheory.LFixDPf

end
