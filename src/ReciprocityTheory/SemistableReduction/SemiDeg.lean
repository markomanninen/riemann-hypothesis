module

public import ReciprocityTheory.SemistableReduction.SemiDegZA
public import ReciprocityTheory.SemistableReduction.SemiDegA
public import ReciprocityTheory.SemistableReduction.SemiDegB
public import ReciprocityTheory.SemistableReduction.SemiDegC
public import ReciprocityTheory.SemistableReduction.SemiDegD

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

theorem semiDeg_holds (hD : DegAddStatement) : SemiPointStatement :=
  SemiPt.semiPoint_of wittBasis_holds latDegBasis_holds integralIndex_holds selfDualIndex_holds
    (gradedExt_holds latDegBasis_holds hD) absDet_holds

end ReciprocityTheory.MultiplicativeHeights
