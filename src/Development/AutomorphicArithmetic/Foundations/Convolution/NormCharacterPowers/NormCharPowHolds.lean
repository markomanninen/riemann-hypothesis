module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.ZeroExp
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.AbsCount2
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LogAsym
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.ClassChar2
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Decomp
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SysEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.CoverEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.UnitOfPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.FibreCG
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.TwoParts
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftSum
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.PartBOfDecomposition
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

@[expose] public section

open PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

theorem count_holds : Count := count (absCount2 bcSum_holds zeroExp logAsym) sysEx (coverEx decomp)

theorem normCharPow_holds : NormCharPow := normCharPow count_holds

theorem fibreCG_holds : FibreCG := fibreCG classChar2 count_holds normCharPow_holds

theorem fibre_holds : Fibre := fibre fibreCG_holds

theorem twoParts_holds : TwoParts := twoParts classChar2 count_holds normCharPow_holds

theorem partA_holds : PartA := by
  intro E _ _ _ n P ι _ m Ps hn hm hι h
  obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E Unit ι (fun _ => n) m (fun _ => P) Ps (fun _ => hn) hm
    (h.mono fun w ⟨C, B, h1, h2, h3⟩ => ⟨fun _ => C, B, fun _ => h1, h2, by simp [h3]⟩)
  have := Fintype.card_congr s
  simp at this
  omega

end UpperTheory.ConvolutionTheory.R
