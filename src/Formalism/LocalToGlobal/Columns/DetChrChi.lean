module

public import Formalism.LocalToGlobal.Columns.RecChainUnfOne
public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalToGlobal.Columns.WordFin
public import Formalism.LocalToGlobal.Columns.TiedCB
public import Formalism.LocalToGlobal.Columns.TiedLv
public import Formalism.LocalToGlobal.Columns.RecLevelLocF
public import Formalism.LocalToGlobal.Columns.TiedVal
public import Formalism.LocalToGlobal.Columns.TiedValRat
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.TiedAtT
public import Formalism.LocalToGlobal.Columns.TiedValBwG
public import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
public import Formalism.LocalToGlobal.Columns.TiedUpDnA
public import Formalism.LocalToGlobal.Columns.TiedCls
public import Formalism.LocalToGlobal.Columns.TiedXp
public import Formalism.LocalToGlobal.Columns.TiedGlPl
public import Formalism.LocalToGlobal.Columns.TiedGlMat
public import Formalism.LocalToGlobal.Columns.RecLevelDiv
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.HermitianForms.DefsChi
public import Formalism.LocalToGlobal.Columns.TiedGlSplit
public import Formalism.LocalToGlobal.Columns.TiedXpU
public import Formalism.LocalToGlobal.Columns.InputsGenus
public import Formalism.LocalToGlobal.Columns.TiedTilA
public import Formalism.LocalToGlobal.Columns.TiedXpT
public import Formalism.LocalToGlobal.Columns.Record
public import Formalism.LocalToGlobal.Columns.NonDeg
public import Formalism.LocalToGlobal.Columns.LevPackFrLat
public import Formalism.LocalToGlobal.Columns.HermOwed
public import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
public import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
public import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneAtT
public import Formalism.LocalToGlobal.Columns.LastVectorMemSpan
public import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.ColInst
public import Formalism.LocalToGlobal.Columns.InputsWeyl
public import Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower
public import Formalism.GL3MeanSquares.HookFormulaTorsion.HilbertSchmidtHalfBound
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.LogRatioLowerBoundOfLogVandermondeGap
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.UpperPlaceHolds
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.VandNSuccRight
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hspan : Submodule.span E (stdLat E n : Set (Sp E n)) = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    simpa using (single_mem_stdLat (E := E) (n := n) i 1)
  have hlat := Formalism.UG.P.csGlob_lattice (F := F) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) hspan x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.toIsLattice.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rel

end DetChrChi

end Formalism.L2.Col
