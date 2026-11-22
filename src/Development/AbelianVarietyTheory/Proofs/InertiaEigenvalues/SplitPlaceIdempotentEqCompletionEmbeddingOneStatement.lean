module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceIdempotentEqCompletionEmbeddingOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_idempotent_eq_completionEmbedding_one : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → e = ι 1 := by
  first | exact @GlobalTheory.IdemIota.idemAt_eq_iota_one | exact GlobalTheory.IdemIota.idemAt_eq_iota_one | (intros; apply GlobalTheory.IdemIota.idemAt_eq_iota_one <;> assumption)
