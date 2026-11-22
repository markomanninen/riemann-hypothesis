module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht

section Ball

variable {C : Type} [NormedField C] [IsUltrametricDist C]

end Ball

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure PtAt (Z : Mdl Y i₀) (C : SCF p) : Type where
  P : PointsOfFlagModel.PtC (Y Z.i) C
  z : Sp ↥(intO ↥C.S) ⟶ Z.X
  z_π : z ≫ Z.π = P.yt

namespace PtAt

variable {Z : Mdl Y i₀} {C : SCF p} (y : PtAt Z C)

def gen : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ y.z

end PtAt

structure Fam (Y : LocalSystem Xo p W) (i₀ : Idx H p) (C : SCF p) : Type where
  pt : ∀ Z : Mdl Y i₀, PtAt Z C
  compat : ∀ Z₁ Z₂ : Mdl Y i₀, Corr Z₁ Z₂ → NatImg Z₁ Z₂ (pt Z₁).gen (pt Z₂).gen

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

abbrev idx0 (ct : At S κ p) : Idx A.H p := ⟨κ.l, κ.c, κ.good p ct.hp⟩

structure DVP (ct : At S κ p) : Type where
  C : SCF p
  K : Subfield ↥C.S
  closed : IsClosed (K : Set ↥C.S)
  dvr : IsDiscreteValuationRing ↥(intO ↥K)
  dense : Dense {x : ↥C.S | IsAlgebraic ↥K x}
  fam : Fam ct.Y (idx0 ct) C
  rat : ∃ w : Sp ↥K ⟶ ct.YY.X, spMap K.subtype ≫ w = (fam.pt ct.YY).gen

variable {ct : At S κ p}

structure Ext (y : DVP ct) : Type where
  L : Subfield ↥y.C.S
  le : y.K ≤ L
  fin : (Subfield.inclusion le).Finite
  π : ↥(intO ↥L)
  irr : Irreducible π

variable {y : DVP ct}

variable {Z : ct.Mdl} {e : Ext y}

end GlobalTheory.LocM.Cht
