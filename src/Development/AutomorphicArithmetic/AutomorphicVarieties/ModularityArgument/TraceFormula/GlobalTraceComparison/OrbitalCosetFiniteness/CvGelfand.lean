module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CvHecke
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeckeGelfandPair

@[expose] public section

open GlobalTheory.BCT UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

theorem cvGelfand : CvGelfand :=
  _root_.UpperTheory.Reformulated.B.HeckeGelfandPair.cvGelfand

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
