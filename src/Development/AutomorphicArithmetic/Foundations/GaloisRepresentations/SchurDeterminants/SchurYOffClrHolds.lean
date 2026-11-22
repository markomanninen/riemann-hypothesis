module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.FibreSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Vdm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PMixDet
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYClrOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PPairSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PVdmSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PPairCount
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.POffPow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.POffRed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PHomog
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurDetOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.WeylTieOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PESpan
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PExpand
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PExtract
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseSub
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseOff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseCoset
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PInterp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PInterpNF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PFibre
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PFibreOff

@[expose] public section

noncomputable section

open Finset

namespace UpperTheory.Gal.Schur

theorem SchurYClr_holds : SchurYClr := (schurYClr_of tie mixDet).1
theorem SchurYOffClr_holds : SchurYOffClr := (schurYClr_of tie mixDet).2
theorem VdmSplit_holds : VdmSplit := vdmSplit_of pairSplit
theorem SchurY_holds : SchurY := schurY_of SchurYClr_holds VdmSplit_holds
theorem SchurYOff_holds : SchurYOff :=
  schurYOff_of (offClrRed_of (offClrPow_of SchurYOffClr_holds VdmSplit_holds (pairCount_of pairSplit)))
    VdmSplit_holds
theorem SchurHomog_holds : SchurHomog := schurHomog
theorem SchurDet_holds : SchurDet := schurDet_of tie
theorem WeylTie_holds : WeylTie := weylTie_of tie
theorem SpanE_holds : SpanE := spanE_of eSpanMul
theorem DenseCoset_holds : DenseCoset := denseCoset_of denseSub spanTop denseOff
theorem Interp_holds : Interp := interp_of (spanProd_of SpanE_holds) expand extract DenseCoset_holds
theorem InterpNF_holds : InterpNF := interpNF_of Interp_holds
theorem Fibre_holds : Fibre := fibre_of SchurY_holds schurHomog SchurDet_holds
theorem FibreOff_holds : FibreOff := fibreOff_of SchurYOff_holds schurHomog SchurDet_holds
theorem FibreSum_holds : FibreSum := fibreSum_of InterpNF_holds Fibre_holds FibreOff_holds

end UpperTheory.Gal.Schur
