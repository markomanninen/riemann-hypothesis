module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementEig
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ProvisionExtensionLink
public import Mathlib
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DetIdealsKernelNormOne
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.GMConjTranspose
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdeal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Reduction
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.EqPOf
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JArith
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantOfTrianglesData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.OneEntryMem
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.PullMulRight
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNormOne
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemStandardThetaLatticeIffAdelicIdeal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.FinrankRow
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuConc
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdealAlt
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.CharacterFactorUnitaryAction
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ReductionOf
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFacts
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLComm
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLInput
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLLaw
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMain
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMat
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLTop
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.RightMoveTrianglesOfUnit
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Family
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfArith
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndepOfGen
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HermitianPairingIntegral
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfTrace
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopIso
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopNorm
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFourSq
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.SelfDual
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdLat
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ThIndep

@[expose] public section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (cmL CmOK matH stdLat pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.GD (LocNorm)
open Formalism.L2.AlgTh (KerStd lamF)

section Defs

variable {D : Car} {X : Fields} (s : Seam D X)

def Seam.flatV (a b : ℕ) : (DVar X.Tau a b → ℂ) ≃ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b where
  toFun z := fun τ i j => z (s.iT.symm τ, i, j)
  invFun w := fun k => w (s.iT k.1) k.2.1 k.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by funext k; simp
  right_inv w := by funext τ i j; simp

def Seam.laF (T : Formalism.L2.Ker.Cd.TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) :
    AddSubgroup (DVar X.Tau a b → ℂ) :=
  (Formalism.L2.Ker.Cd.TaylorLogMetric.La D T L L').comap (s.flatV a b).toLinearMap.toAddMonoidHom

def Seam.StdAtP (p : ℕ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : Prop :=
  Formalism.L2.Ker.Cd.TaylorLogMetric.EqAt D p (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D n) (s.lat N)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def Base.IsCm (a₀ : ℕ) (b₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) : Prop :=
  B.L = cmL a₀ b₀ D.host.d ha hd lam hlam ∧ B.ω₀ = lam * a₀

end Defs

def LamTie : Prop :=
  ∀ (D : Car) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), s.Ok →
    lamF (ambOf s B χ cD) N N' = s.laF B.tor (s.lat N) (s.lat N')

end Formalism.L2.Ker.Cd
