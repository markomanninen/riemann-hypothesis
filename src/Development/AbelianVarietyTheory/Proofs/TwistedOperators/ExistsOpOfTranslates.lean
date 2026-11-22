module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VectorLevelCharacters
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeClassSums

section Linear

variable {L : Type} [Field L] {σ : L →+* ℂ} {H : Type} [AddCommGroup H] [Module ℂ H]

end Linear

section Group

open Formalism.IndefR.Bridge

variable {G : Type} [Group G]

end Group

section Row

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {R}


set_option maxHeartbeats 1000000 in
theorem span_jV (hV : R.models_HV) (hj : R.models_jV) (i : Fin D.R.m) (t : T0) : Submodule.span ℂ (Set.range (R.jV i t)) = ⊤ := by
  apply Submodule.map_injective_of_injective (hV i t).1
  rw [Submodule.map_span, Submodule.map_top, (hV i t).2.1, ← Set.range_comp]
  have h1 : (⇑(R.HV i t).e ∘ ⇑(R.jV i t)) = ⇑((R.B.L i t).pres.extL) := funext fun x => hj i t x
  rw [h1]
  exact GlobalTheory.PresBasic.ext_span (R.B.L i t).pres

end Local

section Comparison₂

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

end Comparison₂

end Row

end GlobalTheory.HeckeClassSums
