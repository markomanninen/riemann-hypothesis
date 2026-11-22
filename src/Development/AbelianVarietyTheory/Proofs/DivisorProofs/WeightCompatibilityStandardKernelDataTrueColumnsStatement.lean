module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightCompatibilityStandardKernelDataTrueColumns
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  first | exact @GlobalTheory.ColRows.weightTie_of_stdKer | exact GlobalTheory.ColRows.weightTie_of_stdKer | (intros; apply GlobalTheory.ColRows.weightTie_of_stdKer <;> assumption)
