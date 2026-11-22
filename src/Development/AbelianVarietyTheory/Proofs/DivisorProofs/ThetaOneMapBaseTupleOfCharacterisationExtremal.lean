module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRow0OfRowsSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhRatOfSerCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitModulusConstantsEquivariantDictionaryStatement

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapTies

theorem oneMapRow0_of_ties_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio O i hpins
  have h := GlobalTheory.T.exists_unitModulus_constants_equivariant_dictionary hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i Unit (fun _ => A.μ0) (O i) hpins.2
  obtain ⟨cc, -, u, -, hequiv, hser, hid⟩ := h
  exact GlobalTheory.OneMapBase.oneMapRow0_of_rows T R κ v₀ O i (u • cc) 1 hpins hequiv hid
    (GlobalTheory.PhRatCommon.phRat_of_ser_core D G Pl0 T0 A T R F κ v₀ hR ht O i hpins (u • cc) hser
      (GlobalTheory.T.exists_cuspForm_classSum_normalisedData hCI D G Pl0 T0 A T R F κ v₀ hR ht i _ _ (O i) hpins.2 ()) hequiv)

end GlobalTheory.OneMapTies
