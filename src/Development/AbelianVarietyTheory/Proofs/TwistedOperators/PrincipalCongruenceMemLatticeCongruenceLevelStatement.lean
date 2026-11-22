module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalCongruenceMemLatticeCongruenceLevel
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_mem_latticeCongruenceLevel : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (g : ℕ), 1 ≤ g → ∀ k ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kg g, Formalism.IndefR.Eqv.UI.brg fr (1, k) ∈ Formalism.IndefR.Lev.levA V (congLev D.sp.cm V.gram fr.Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})) := by
  first | exact @GlobalTheory.CongLevelInst.kg_mem_levA | exact GlobalTheory.CongLevelInst.kg_mem_levA | (intros; apply GlobalTheory.CongLevelInst.kg_mem_levA <;> assumption)
