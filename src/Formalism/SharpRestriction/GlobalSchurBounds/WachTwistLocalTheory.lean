module

public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.LocalRingCardinality.DataKerP
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions Classical NumberField

section Gen

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

end Gen

section Fm

variable (D : D7) (u : D.what₂.Word)

end Fm

section Tw

variable (D : D7)

variable {D}

variable (D)

structure PendTw (u : D.what₂.Word) (μ : D.what₂.Tup) where

  clsLat : letI := D.host.cmStar; ∀ i, (D.chTw u μ).cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V
  clsLat_lat : letI := D.host.cmStar; ∀ i c, Submodule.IsLattice D.host.E (clsLat i c)

  detCls : ∀ i, (D.chTw u μ).cls i → D.Dt

  xi : D.Dt →* ℂˣ
  xi_fin : ∃ n : ℕ, 0 < n ∧ ∀ x, xi x ^ n = 1
  trueColumnChoices_heckeChar_reference_eq_one : μ = D.what₂.mu0 → xi = 1

  rhoDet_eq_inv_muTilde_chiD_pow : ∀ i (c : (D.chTw u μ).cls i),
    (D.chTw u μ).rhoDet i c = (((D.muTil (i + 1) (detCls i c) * xi (detCls i c))⁻¹ *
      (D.chiD (detCls i c)) ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  rhoDetPrime_eq_muTilde_mul_chi_pow : ∀ i (c : (D.chTw u μ).cls (i + 1)),
    (D.chTw u μ).rhoDet' i c = ((D.muTil (i + 1) (detCls (i + 1) c) * xi (detCls (i + 1) c) *
      (D.chiD (detCls (i + 1) c)) ^ ((((D.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)

  c0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  y0 : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  zero_class_lattice_eq : ∀ c, clsLat 0 (c0 c) = D.clsLat u 0 c
  zero_class_det_eq : ∀ c, detCls 0 (c0 c) = D.detCls u 0 c

  zero_identification_is_identity : ∀ φ c y, D.e0Tw u μ φ (c0 c) (y0 y) = φ c y

variable {D}

def colTw (u : D.what₂.Word) (μ : D.what₂.Tup) (x : Vl D u 0) : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ :=
  (D.chTw u μ).col (D.e0Tw u μ ((D.fm u).emb 0 x))

def TwistedT5ColumnBound (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    ∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ VV D u w, ((D.R.t : ℝ) + 1 + 2 * Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      ∀ x ∈ Nlam D u w, ∃ y ∈ (T.fm u μ).S D.R.m w, (T.fm u μ).emb D.R.m y = tpow D u e • colTw u μ x

def TupleChainSharpColumnValuation (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w))

end Tw

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

section Ref

open Formalism.BasicNotions.DV

variable {D : D7}

end Ref

end Formalism.MainNotions.product_first_zeroth_parts
