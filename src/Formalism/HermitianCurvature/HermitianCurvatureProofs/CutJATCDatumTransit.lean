module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSStab

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem datum_transitivity_holds : DatumTransit := datumTransit_of_cut datum_transit_existence datum_transit_stabilizer

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
