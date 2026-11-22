module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PAscAll
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChord
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ProjOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStages
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTens
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopGap
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem ascAll_of_rest (hS : Slice) (hP : Pr) (hI : IndMap) (hT : StringStep) : AscAll :=
  ascAll_of (dich_of dict_holds finTr_holds killPoly_holds) (expFin_of dict_holds finTr_holds) expNeg_holds hS
    (chord_of expTw_holds sqIntCrit_holds) (proj_of hP sliceTens_holds hI) infInd2_holds hT (stages_of hI)

end PositivityTheory.Rg.Rs
