module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCVPosIdele
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.Desc
open GroundTheory.Automorphic.Reduction (adelicBorel maxCompact posIdele diagUnits)
open scoped ENNReal
attribute [local instance] borelH

noncomputable section
namespace GlobalTheory.CompanionTheory.PiVec

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.CompanionTheory.PiVec
end
