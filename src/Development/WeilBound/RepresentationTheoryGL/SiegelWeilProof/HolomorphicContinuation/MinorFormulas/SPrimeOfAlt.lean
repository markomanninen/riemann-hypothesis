module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrimeOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBClose
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.IntegrableOfBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainA

@[expose] public section

namespace PositivityTheory.Rg.Sw.SP

theorem sPrime_of : SPrimeOf :=
  sPrime_of' PositivityTheory.Rg.Sw.WR.B.clsBound PositivityTheory.Rg.Sw.WR.K.GB.clsGainB PositivityTheory.Rg.Sw.WR.ibp PositivityTheory.Rg.Sw.WR.I.integr
    PositivityTheory.Rg.Sw.WR.Z.chain PositivityTheory.Rg.Sw.WR.Z.ext

end PositivityTheory.Rg.Sw.SP
