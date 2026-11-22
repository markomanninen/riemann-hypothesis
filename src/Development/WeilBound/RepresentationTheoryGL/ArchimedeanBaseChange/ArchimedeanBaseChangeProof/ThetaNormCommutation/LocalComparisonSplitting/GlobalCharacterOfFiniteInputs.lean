module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountIsInvInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormaliserUnconj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantOfRightInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoordinate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScalarOfCentral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqSign
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialFiniteAdeles
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRegEllIffMemEll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjugateEquivalence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigenbasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOfBounded
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitPreimageEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRatCentTwConj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PWeylAt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTermOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfHolds

@[expose] public section

namespace PositivityTheory.Rg.BcB.G8

open GlobalTheory.CompanionTheory

theorem translation_existence_holds : TranslEx := LocalThetaTranslation.translEx

theorem lefschetz_pair_holds : LefPair := GlobalTheory.CompanionTheory.LefPair.lefPairOf EllipticTwist.ellDiag weylAt_holds LocalThetaTopology.topo

theorem global_character_of_finite_inputs (hK : KfOC) (hL : FinLevel) (hF : FinHalf) : G4 :=
  have hA : AdelEq := AdelEqProof.adelEqOf TranslAdele.translAd
  global_character_of_holds
    (termOf_holds (QSplitPf.qSplitOf QuotNorm.qIndep) HaarProd.haarSplit LocalThetaTopology.topo CompIsoProof.compIso hK hL hF hA
      TwistCent.centEq NormPoly.polEq (EllProp.ellProperOf EllipticTwist.ellDiag DiagProperProof.diagProper LocalThetaTopology.topo))
    (GlobalTheory.CompanionTheory.OrbInv.orbInvOf (QConjug.qConjOf_holds QuotNorm.qIndep) LocalThetaTopology.topo)
    (GlobalTheory.CompanionTheory.AdelCont.adelContOf hA hL CompIsoProof.compIso LocalThetaTopology.topo) GlobalTheory.CompanionTheory.ClassBij.classBij NormPoly.polEq

end PositivityTheory.Rg.BcB.G8
