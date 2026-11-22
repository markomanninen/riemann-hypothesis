module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamSphOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLiftOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CoreId
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TorusCharComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.LocGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJHolds

@[expose] public section

theorem UpperTheory.ConvolutionTheory.Sph.ramSph : UpperTheory.ConvolutionTheory.Sph.RamSph :=
  UpperTheory.ConvolutionTheory.Sph.ramSphOf UpperTheory.Gal.Join.locGal (UpperTheory.Gal.Join.liftGood
    (UpperTheory.Gal.Join.coreId UpperTheory.Gal.InertialTypesAlt.G.varEx UpperTheory.Gal.InertialTypesAlt.G.varTrace UpperTheory.Gal.InertialTypesAlt.L.elemPairJ_holds))

theorem UpperTheory.ConvolutionTheory.Sph.quadLift : GlobalTheory.GalCut.QuadLift := UpperTheory.ConvolutionTheory.Sph.quadLiftOf UpperTheory.ConvolutionTheory.Sph.ramSph
