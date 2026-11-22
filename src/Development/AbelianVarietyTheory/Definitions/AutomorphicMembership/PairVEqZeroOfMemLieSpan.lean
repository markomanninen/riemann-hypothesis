module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Generic

variable {p : ℕ} [Fact p.Prime] {C : SCF p} {Λ : Type} [CommRing Λ] [StarRing Λ]
  (P : Point p (fldVal C) ↥(intO ↥C.S) Λ)

def tateIncl : P.T →+ P.V := (TensorProduct.mk ℤ_[p] ↥C.S P.T 1).toAddMonoidHom

def htMap : P.T →+ P.OmC := P.inclOm.toAddMonoidHom.comp P.al₀.toAddMonoidHom

def lieSpan : Submodule ↥C.S P.V := Submodule.span ↥C.S (P.latLie : Set P.V)

theorem span_tateIncl : Submodule.span ↥C.S (Set.range (tateIncl P)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul c t =>
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨t, rfl⟩)

theorem alC_tateIncl (t : P.T) : P.alC (tateIncl P t) = htMap P t := P.alC_tmul 1 t

end Generic

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

def htPt {Z : ct.Mdl} (y : ct.Pt Z) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Point p (fldVal y.C) ↥(intO ↥y.C.S) (𝓞 D.host.E) :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  htPoint (ct.dat y)

def psiEmb (D : D7) (τ : PsiT D) : D.host.E →+* ℂ := DV.tauEmb D (D.eTau.symm τ)


open Classical in
def eigProj {Z : ct.Mdl} (y : ct.Pt Z) (σ : D.host.E →+* ℂ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; (ct.htPt y).V →ₗ[↥y.C.S] (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  proj (isSplitting_embInt y.P) (ct.htPt y).actV σ

end At

def htpTrue (ct : At S κ p) : HTpSt ct :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  { Tp := fun y => (ct.htPt y).T
    tpAdd := fun _ => inferInstance
    OmV := fun y => (ct.htPt y).OmC
    omAdd := fun _ => inferInstance
    omMod := fun y => (inferInstance : Module ↥y.C.S (ct.htPt y).OmC)
    om := fun y => (ct.htPt y).latOm.toAddSubgroup
    ht := fun y => htMap (ct.htPt y)
    om_smul := fun y a ha _ hv => (ct.htPt y).latOm.smul_mem (⟨a, ha⟩ : ↥(intO ↥y.C.S)) hv
    TC := fun y => (ct.htPt y).V
    tcAdd := fun _ => inferInstance
    tcMod := fun y => (inferInstance : Module ↥y.C.S (ct.htPt y).V)
    iT := fun y => tateIncl (ct.htPt y)
    iT_span := fun y => span_tateIncl (ct.htPt y)
    htC := fun y => (ct.htPt y).alC
    htC_iT := fun y => alC_tateIncl (ct.htPt y)
    psiC := fun y => (ct.htPt y).pairV
    lieGt1 := fun y => lieSpan (ct.htPt y)
    eT := fun y τ => ct.eigProj y (At.psiEmb D τ) }

namespace HTp

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

end HTp

end GlobalTheory.LocM
