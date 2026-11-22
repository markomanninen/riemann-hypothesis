module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelTests

section Ext
variable {V W : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]

end Ext

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem isNsmul_b {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, hl⟩ := H
  have key : ∀ (n : ℕ) (hn : n < k + 1), (gs ⟨n, hn⟩).b = g.b ^ n := by
    intro n
    induction n with
    | zero => intro hn; rw [pow_zero]; exact h0.1
    | succ n ih =>
      intro hn
      have e := (hs ⟨n, by omega⟩).1
      rw [pow_succ, ← ih (by omega)]
      exact e
  rw [← hl]
  exact key k (Nat.lt_succ_self k)

end Tors

end GlobalTheory.UU.RelTests
end
