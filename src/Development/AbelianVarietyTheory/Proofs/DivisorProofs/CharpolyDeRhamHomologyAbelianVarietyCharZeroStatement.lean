module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charZero : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  exact @GlobalTheory.DeRhamCharpolyZero.charpoly_push
