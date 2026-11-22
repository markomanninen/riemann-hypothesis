module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainTieAndV0Onto
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColNormExistsImNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CxFactsOfPrims
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapReferenceTupleGoodPartOntoRows
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadOfMatrixTie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImNeZeroOfTotallyComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ICCptEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGAMemGFset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeamExLinCpt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqIntegralOfAe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodOperatorSpectrum

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.KernelJoin

theorem heq_of_reindex {K W Mem : Type} [Field K] (a : Mem → ℕ) {V : W → Type} [∀ u, AddCommGroup (V u)]
    [∀ u, Module K (V u)] {Z : Mem → Type} {Y : W → Type} (b : ∀ x, Fin (a x) → Z x) (g : ∀ u, V u → Y u)
    (w w' : W → Mem) (ν : ∀ u, (Fin (a (w u)) → K) ≃ₗ[K] V u) (ν' : ∀ u, (Fin (a (w' u)) → K) ≃ₗ[K] V u)
    (hw : w = w') (hν : HEq ν ν') (h : ∀ u i, HEq (b (w' u) i) (g u (ν' u (Pi.single i 1)))) :
    ∀ u i, HEq (b (w u) i) (g u (ν u (Pi.single i 1))) := by
  subst hw
  cases hν
  exact h

theorem smul_apply_eq_of_eq {A B : Type} [AddCommGroup B] [Module ℂ B] (f : A → B) {a a' : A} (h : a = a')
    (k κ : ℂ) {b : B} (hb : f a' = κ • b) : k • f a = (k * κ) • b := by
  rw [h, hb, mul_smul]

end GlobalTheory.Mem.SJ.KernelJoin
