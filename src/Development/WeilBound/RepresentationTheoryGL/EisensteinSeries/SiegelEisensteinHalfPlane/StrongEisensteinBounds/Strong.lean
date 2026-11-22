module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimateStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimateStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopologyStatement

@[expose] public section

namespace PositivityTheory.Rg.SwEis.Hd

open PositivityTheory.RgEis.Hd

theorem eisStrong : PositivityTheory.Rg.Sw.Glob.EisStrong :=
  GlobalTheory.T.eisenstein_topology dict dictInf (cmGood_of stdGood dict dictInf) grpTop bdetLaw extLaw (parLaw_of bdetLaw extLaw grpTop)
    sgAll GlobalTheory.T.standard_section_exists (GlobalTheory.T.eisenstein_iwasawa_estimate (GlobalTheory.T.chart_section_exists dict dictInf GlobalTheory.T.standard_section_exists)) (GlobalTheory.T.scalar_section_exists secLaw (wallLaw_of secLaw))
    (GlobalTheory.T.eisenstein_far_estimate htLip) GlobalTheory.T.eisenstein_gluing

end PositivityTheory.Rg.SwEis.Hd
