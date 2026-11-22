module

public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.Assembly
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IotaBounded
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.EqToBdRPlusOfBounded

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

def iotaP : ACris.ACris ℂ_[l] l →+* Formalism.Per6.BdRp l := ACris.iota ℂ_[l] l

def jOC : Reformulated.AutPerF.Acris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdRPlus l (Cmp6.OC l) :=
  ((Cmp6.cP l).symm.toRingHom.comp (iotaP l)).comp (Cmp6.cA l).toRingHom

end Formalism.BasicNotions.CmpTie.Incl
