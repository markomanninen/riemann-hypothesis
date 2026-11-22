module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.SemistableReduction.TorusLexA
public import ReciprocityTheory.SemistableReduction.TorusLexC

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

theorem torusLex_holds (hBasic : TorusMeanBasicStatement) (hCoeff : TorusCoeffStatement) :
    TorusLexStatement ∧ TorusL2Cauchy :=
  ⟨TorusLexOrder.torusLex_of hBasic hCoeff, TorusLexOrder.torus_l2_cauchy_of_basic hBasic⟩

end ReciprocityTheory.MultiplicativeHeights
