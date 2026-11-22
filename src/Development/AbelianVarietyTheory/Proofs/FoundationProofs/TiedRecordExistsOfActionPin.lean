module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnTies

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure RunData (J : CoreJ D) : Type 1 where

  loc : In66 J.Q

  nab : ∀ j, NabV (J.Q.Xo j) J.Q.c

  dδ : ∀ j n, DeltaDat (J.Q.Xo j) J.Q.c n

  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ

  half₂ : Ideal (𝓞 D.host.E)

abbrev RunData.full {J : CoreJ D} (r : RunData J) : Full D :=
  ⟨⟨J.toCore, r.loc, r.nab, r.dδ⟩, J.cE, J.chiW, J.x₀, J.iota, r.xi, r.half₂⟩

section Cusp

variable (B : WeightFamilies.Prov D) {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K] [Algebra B.KO K] {n : ℕ}

def supSpan (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) : Submodule (𝓞 K) (Fin n → K) := spanK z (B.Mlat j w : Set _)

def shortSpan {P6 : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.PJ D B P6 j) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) :
    Submodule (𝓞 K) (Fin n → K) := spanK z (X.shortTh w : Set _)

def scaledSpan {P6 : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (wL wF : WeightFamilies.Wt D j) (nT : ℕ) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) : Submodule (𝓞 K) (Fin n → K) :=
  spanK z {F | X.inc w F ∈ X.Theta (scalOfP B hinj EX p w wL wF nT) w wL wF nT}




omit [NumberField K] in
theorem exists_cuspRep_of_injective (f : B.Cusp j w →ₗ[B.KO] (Fin n → K)) (hf : Function.Injective f) {P : Type} [Group P]
    (σ : Representation K P (Fin n → K)) (a : P → B.Cusp j w → B.Cusp j w) (ha : ∀ g F, f (a g F) = σ g (f F)) :
    ∃ ρ : Representation B.KO P (B.Cusp j w), ∀ g F, ρ g F = a g F := by
  refine ⟨{ toFun := fun g =>
              { toFun := a g
                map_add' := fun F F' => hf (by rw [map_add (f := _), ha, ha, ha, map_add (f := _), map_add (f := _)])
                map_smul' := fun c F => hf ?_ }
            map_one' := LinearMap.ext fun F => hf ?_
            map_mul' := fun g g' => LinearMap.ext fun F => hf ?_ }, fun _ _ => rfl⟩
  · rw [RingHom.id_apply, map_smul, ha, ha, map_smul, LinearMap.map_smul_of_tower]
  · change f (a 1 F) = f F
    rw [ha, map_one, one_apply_eq_self]
  · change f (a (g * g') F) = f (a g (a g' F))
    rw [ha, ha, ha, map_mul, mul_apply_eq_comp]

end Cusp

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem ActionPin.exists_rep {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {i : Fin D.R.m}
    {ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)}
    (ha : ActionPin h fw i ℓ) {P : Type} [Group P] (inc : P →* G) :
    ∃ ρ : Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)),
      IsLevAct T.toTop h ((i : ℕ) + 1) (κ i) (fun g => ℓ (inc g)) fun g F => ρ g F := by
  obtain ⟨a, h1, h2⟩ := ha
  obtain ⟨ρ, hρ⟩ := exists_cuspRep_of_injective (recB h.toLawsCore) (cuspTo h fw i) (cutTo_spec fw i).1
    ((R.FW i).ρ.comp inc) (fun g => a (inc g)) fun g F => h2 (inc g) F
  exact ⟨ρ, fun g F => (congrArg Subtype.val (hρ g F)).trans (h1 (inc g) F)⟩

section Tied

variable (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData T.J) (hr : ∀ v, LawsP (r v).full.toTop)
  (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (ι : Bs.J → Fin D.R.m) (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)
  (ℓ : ∀ i, G → (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ)
  (ρ : ∀ i, Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))))
  (O : OnObj S P oc)
  (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))


end Tied

def blankObj (D : D7) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
    (n : Bs.J → ℕ) : OnObj S P oc where
  nZ := n
  ρ _ := 1
  U := ⊥
  ψ := 1
  V₀ _ := ⊥
  e _ := 0
  Ms _ := ⊥
  φ _ := 0
  Th1 _ _ := ⊥
  Th _ _ := ⊥
  ThK _ _ := ⊥
  Th0 _ _ := ⊥
  ThJ _ _ := ⊥
  X₃ _ _ := ⊥
  σ := 0
  a := 0
  E := 0
  r1 := 0
  r2 := 0
  pde := D.host.pde
  ε0 := 0
  nX := 0
  θ' _ _ := 0
  eX _ _ := 0
  pr _ _ := 0
  Mt _ _ := ⊥
  nnK := 0
  Jp := 0
  k := D.R.k
  m := D.R.m
  f := D.R.f
  bp := 0
  Sc := 0
  eta := 0
  T := 0
  DF := 0
  X2 := 0
  x := 0
  eps := 0
  vd := 0
  rr := D.R.r
  de2 := 0
  Nc := 0
  wt := 0
  th := 0
  ad := 0
  T2 := D.host.T2.card
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  dd := D.host.d
  sm := D.host.small

section Exists

variable (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData T.J) (hr : ∀ v, LawsP (r v).full.toTop)
  (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
  (ι : Bs.J → Fin D.R.m) (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)

end Exists

end GlobalTheory.OnTies
