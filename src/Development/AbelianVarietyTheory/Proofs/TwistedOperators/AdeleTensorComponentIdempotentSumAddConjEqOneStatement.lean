module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z, compFin D.host.F D.host.E ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (e + cA D e) = 1 := by
  first | exact @GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | exact GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | (intros; apply GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one <;> assumption)
