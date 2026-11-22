module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.TiedVal
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.TiedValRat
public import Formalism.LocalToGlobal.Columns.CoefModAt
public import Formalism.LocalRingCardinality.PosOfIsomEmb
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalRingCardinality.DataArith
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem ptField_main : ∀ D : D7, IsTotallyComplex D.what₂.LL ∧ (∃ v0 : InfinitePlace D.what₂.LL, Formalism.DivisionValues.IsConjAt v0) ∧ ∀ (u : D.what₂.Word) (c : (D.fm u).clsP), Nat.card ((D.fm u).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  intro D
  refine ⟨D.tcLL, GlobalTheory.isConjAt_exists_main D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩, ?_⟩
  intro u c
  exact (Subgroup.card_dvd_of_injective _ ((D.fm u).stabMap_inj c)).trans
    ((D.mem u).C.dvd_DGam _ le_rfl _)

end GlobalTheory
