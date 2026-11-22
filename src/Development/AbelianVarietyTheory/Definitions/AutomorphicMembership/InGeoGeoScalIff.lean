module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DefiniteSideNonzeroIndexPlacesAnyColumnsScale
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Res

section Geo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {ph : Fin D.R.m → ℂ}


set_option maxHeartbeats 2000000 in
def geoScal (g : GlobalTheory.RealGeo.GeoHalf C R ph) (kap lam err) :
    GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R kap lam err g.fw, g.bar, fun i => GlobalTheory.RealGeo.Upd.updO C R kap lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩


end Geo

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]




def KapFixed (S : RealDat3 D A3 Ks) (κ : ℝ) : Prop :=
  Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
    ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0


open Classical in
def kapNew (S : RealDat3 D A3 Ks) : ℝ := if h : ∃ κ, KapFixed S κ then h.choose else S.kap

theorem kapNew_eq (S : RealDat3 D A3 Ks) {κ : ℝ} (h : KapFixed S κ) : kapNew S = κ := by
  have h' : ∃ κ, KapFixed S κ := ⟨κ, h⟩
  unfold kapNew
  rw [dite_eq_left h']
  obtain ⟨t, p, hp, hl⟩ := h.2
  exact Lift.IsKap.unique h'.choose_spec.1 h.1 t p hp hl

theorem kapNew_of_not (S : RealDat3 D A3 Ks) (h : ¬ ∃ κ, KapFixed S κ) : kapNew S = S.kap := dif_neg h

theorem kapNew_of_scal (S : RealDat3 D A3 Ks) (h : S.scal_kap) : kapNew S = S.kap := by
  by_cases h' : ∃ κ, KapFixed S κ
  · obtain ⟨κ, hκ⟩ := h'
    exact (kapNew_eq S hκ).trans (h κ hκ.1 hκ.2).symm
  · exact kapNew_of_not S h'


variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}



end Generic

end Res

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat








end Dat

end Record

end GlobalTheory.Mem.R3

end
