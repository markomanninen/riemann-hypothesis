module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiBigTheorem.HSChain
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiSymmetry.EqMapSymm
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.PoincareLelongInv
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelongStatement

@[expose] public section

namespace PositivityTheory.Pf1.HilbertSamuelMoriwaki

theorem moriwakiBig_outright : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement :=
  moriwakiBig_of_classicalTheorems PositivityTheory.ResPlug.FromRes.resK
    (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main

theorem hsUse_outright : HSUse :=
  hsUse_of_hypotheses PositivityTheory.ResPlug.FromRes.resK
    (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main

end PositivityTheory.Pf1.HilbertSamuelMoriwaki
