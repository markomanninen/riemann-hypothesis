module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Frm

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {C M : Type} [NormedField C] [IsUltrametricDist C] [AddCommGroup M] [Module C M] {m : ℕ}






end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {x' : Sp T ⟶ X}

end Tangent

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} (y : Z.Pt)

variable {y}




end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

variable {ct}


end GlobalTheory.LocM.Frm
