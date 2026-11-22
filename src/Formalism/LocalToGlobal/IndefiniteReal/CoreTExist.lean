module

public import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.CoreT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Half

variable (P : Formalism.L2.Host.PiBar D.host)


variable (hF : OFull D) (hz : OZeta D) (hN : N1ab)

end Half

section Chr

theorem mem_of_latHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) {x : Fin n → E}
    (h : (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E))) : x ∈ Λ := by
  have key : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)),
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (y i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hs : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩)
      have hv : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
          Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := Submodule.subset_span ⟨x, hx, rfl⟩
      convert Submodule.smul_mem _ (⟨(1 : E) ⊗ₜ[F] a, hs⟩ : Formalism.L2.Herm.intAf F E) hv using 1
      funext i
      show Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (a ⊗ₜ[F] x i) =
        ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rfl
    | zero =>
      convert Submodule.zero_mem (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ) using 1
      funext i
      exact map_zero _
    | add y z _ _ hy hz =>
      convert add_mem hy hz using 1
      funext i
      exact map_add _ _ _
    | neg y _ hy =>
      convert neg_mem hy using 1
      funext i
      exact map_neg _ _
  have hg : x ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    exact key _ h
  rwa [Formalism.UG.P.global_lattice_one_holds F E (Fin n) Λ hfin hsp] at hg

end Chr

section Unif

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}



variable {U : Unf Xo c σ r} {V : HSp D} {dict : GA D V → Σ k, Frame (U.X k).Ψ r} {mu : GA D V → ℂ}

end Unif

section Core

variable (Q : Par D)

variable {Q}

end Core

section Rec

variable (Q : Par D)



variable {Q}

end Rec

section Pg

end Pg

section Rows

section Gen

variable {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (s : E →ₐ[F] E)
  (hs : ∀ e, ∃ f : F, algebraMap F E f = e + s e)

include hs

end Gen

section H90

end H90

end Rows

section Cover

open CategoryTheory

attribute [local instance] Over.cartesianMonoidalCategory

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

end Cover

section IdMap

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

section Cech

variable {X Y : Scheme.{0}}

variable (L : LB X)

variable {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)


end Cech

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}


end IdMap

section Trans

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

include hle

end Trans

section Lat

variable {n : ℕ}

end Lat

section OM

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}



variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec)
  (c' : Coeff T.Q.l) (jL : D.what₂.LL →+* c'.F) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)

variable {T R i v₀ c' jL lev}

end OM

end Formalism.IndefR.CoreT
