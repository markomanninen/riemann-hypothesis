module

public import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthOfLengthEigenLengthProduct
public import ReciprocityTheory.DualLattices.EqZeroOfIsoZero
public import ReciprocityTheory.DualLattices.MatEquivApply
public import ReciprocityTheory.DualLattices.EigenLengthProductStatementHolds
public import ReciprocityTheory.DualLattices.LenEx
public import ReciprocityTheory.DualLattices.MonomialsSpanOfProdEq
public import ReciprocityTheory.DualLattices.EigenLiftsFrobenius
public import ReciprocityTheory.DualLattices.ElementaryDivisorStatement
public import ReciprocityTheory.DualLattices.RankEqRankOfPermAndZero
public import ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatementHolds
public import ReciprocityTheory.DualLattices.FrobeniusBlock
public import ReciprocityTheory.DualLattices.SumX
public import ReciprocityTheory.DualLattices.EmbeddingSeparatingGroup

@[expose] public section

namespace ReciprocityTheory.PGsh.Up

theorem frobenius_of_length_lifts (hLen : LenIdStatement) (hEx : LenExStatement) (hTot : EigenLengthProductStatement)
    (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_length_eigenLengthProduct hLen hEx hTot (core_of (lifts_of hG hE hR) hB hF)

theorem unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement)
    (hR : EigenRankStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  frobenius_of_length_lifts lenId lenEx eigenLengthProductStatement_holds hG hE hR hB hF

theorem frobenius_of_group_divisors_rank (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts hG hE hR monomials_span_of_prod_eq (frob_of hF1 hF2 hF3)

theorem unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound (hG : EmbeddingSeparatingGroupStatement) (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement)
    (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  frobenius_of_group_divisors_rank hG elementary_divisor_statement rank_eq_rank_of_perm_and_zero hF1 hF2 hF3

theorem unramifiedCokernelLength_of_frobeniusLengthBound (hG : EmbeddingSeparatingGroupStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound hG liftMonomialDeterminantStatement_holds frobeniusBlock hF3

theorem frobenius_of_group (hG : EmbeddingSeparatingGroupStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_frobeniusLengthBound hG u7F3

theorem u7 : UnramifiedCokernelLengthStatement :=
  frobenius_of_group embeddingSeparatingGroup

end ReciprocityTheory.PGsh.Up
