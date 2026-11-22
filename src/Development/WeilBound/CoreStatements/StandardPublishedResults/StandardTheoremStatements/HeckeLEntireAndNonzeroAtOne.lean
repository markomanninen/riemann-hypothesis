module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible

@[expose] public section

namespace PositivityTheory.Stage1.PM

theorem gLHoweDuality : GlobalTheory.Published.GLHoweDuality :=
  GlobalTheory.Published.glHoweDuality_holds

theorem borelCasselman : GlobalTheory.Published.BorelCasselman :=
  GlobalTheory.Published.BorelCasselman_holds

theorem quadraticClassFieldTheory : GlobalTheory.Published.QuadraticClassFieldTheory :=
  GlobalTheory.Published.quadraticClassFieldTheory_holds

theorem heckeLEntireAndNonzeroAtOne : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne :=
  GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds

theorem weylBranching : GlobalTheory.Published.WeylBranching :=
  GlobalTheory.Published.weylBranching_holds

end PositivityTheory.Stage1.PM
