module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicTraceCharacterSplitSectionNeOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyExtUnramTwoNotMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnifUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTameRamified
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Filter
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.Inhab

variable {D : D7}

def intGrp (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem mem_intGrp {v : Pl D} {a : AE D} : a ∈ intGrp D v ↔ a ∈ intAt D (· = v) := Iff.rfl

theorem int_mul {v : Pl D} {a b : AE D} (ha : a ∈ intGrp D v) (hb : b ∈ intGrp D v) : a * b ∈ intGrp D v :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2 hb.2⟩

theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a := by
  have h := GlobalTheory.LatAlmostStd.tmul_mem_intAt (D := D)
    (GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) fun w => by rw [map_one]; exact one_mem _) 1
  rw [mul_one] at h
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)), GlobalTheory.IdemSupport.cA_algebraMap _, h,
    fun a => ⟨fun ha => ?_, fun ha => ha ▸ Ideal.mul_mem_right _ _ h.1⟩⟩
  rw [← Algebra.smul_def]
  exact GlobalTheory.LatAlmostStd.smul_eq_of_mem_idAt ha

theorem int_cA {v : Pl D} {a : AE D} (ha : a ∈ intGrp D v) : cA D a ∈ intGrp D v := by
  obtain ⟨ε, hc, -, hid⟩ := exists_idem v
  refine ⟨(hid _).2 ?_, GlobalTheory.IdemSupport.finPart_cA_mem ha.2⟩
  conv_lhs => rw [← hc, ← map_mul, (hid a).1 ha.1]

theorem int_cA_iff {v : Pl D} {a : AE D} : cA D a ∈ intGrp D v ↔ a ∈ intGrp D v :=
  ⟨fun h => by simpa only [Formalism.L2.Theta.cA_cA] using int_cA h, int_cA⟩

theorem mulVec_mem {v : Pl D} {m n : ℕ} {M : Matrix (Fin m) (Fin n) (AE D)} {y : Fin n → AE D} {i : Fin m}
    (h : ∀ j, M i j * y j ∈ intGrp D v) : (M *ᵥ y) i ∈ intGrp D v := by
  simp only [mulVec, dotProduct]
  exact sum_mem fun j _ => h j

def RatInt (v : Pl D) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Prop :=
  ∀ i j, ∀ a ∈ intGrp D v, incA D (M i j) * a ∈ intGrp D v

theorem ae_family {ι : Type} [Finite ι] {x : ι → D.host.E} (hx : x ≠ 0) :
    ∀ᶠ v : Pl D in cofinite, ∀ a, (∀ k, a * incA D (x k) ∈ intGrp D v) ↔ a ∈ intGrp D v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  filter_upwards [eventually_all.2 fun j => GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (x j), GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (x k)⁻¹] with v h1 h2 a
  refine ⟨fun h => ?_, fun h j => by rw [mul_comm]; exact h1 j a h⟩
  have := h2 _ (h k)
  rwa [mul_left_comm, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one] at this

def Std (S : HSp D) (L : Lat S) (v : Pl D) : Prop := ∀ y, y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intGrp D v

theorem ae_std {S : HSp D} {L : Lat S} (h : IsSelfDualC S L) : ∀ᶠ v : Pl D in cofinite, Std S L v :=
  GlobalTheory.LatAlmostStd.eventually_latV_iff D S L (GlobalTheory.ProjXCols.selfDual_isFullLattice S L h)

theorem ae_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) :
    ∀ᶠ v : Pl D in cofinite, ∀ u : WO S T, u ∈ latO S T (LS : Set _) (LT : Set _) (· = v) ↔ ∀ i j, u i j ∈ intGrp D v := by
  filter_upwards [ae_std hS, ae_std hT, GlobalTheory.FinPl.AlmostAll.latA_eq_latV D] with v h1 h2 h3 u
  obtain ⟨ε, -, hε, hid⟩ := exists_idem v
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, h3]
  refine ⟨fun ⟨hm, h⟩ i j => ?_, fun h => ⟨fun i j => (h i j).1, fun y hy => (h2 _).2 fun i =>
    mulVec_mem fun j => int_mul (h i j) ((h1 y).1 hy j)⟩⟩
  have := (h2 _).1 (h (Pi.single j ε) ((h1 _).2 fun k => by
    by_cases hk : k = j
    · subst hk; rw [Pi.single_eq_same]; exact hε
    · rw [Pi.single_eq_of_ne hk]; exact zero_mem _)) i
  rw [mulVec_single] at this
  have e : u i j * ε = u i j := by rw [mul_comm]; exact (hid _).1 (hm i j)
  rw [← e]
  exact this

def RatCols {m n : ℕ} (x : Mx D m n) : Prop := ∀ i, ∃ c : Fin m → D.host.E, c ≠ 0 ∧ ∀ k, x k i = incA D (c k)

theorem RatCols.ae {m n : ℕ} {x : Mx D m n} (h : RatCols x) :
    ∀ᶠ v : Pl D in cofinite, ∀ i a, (∀ k, colMul x i a k ∈ intGrp D v) ↔ a ∈ intGrp D v := by
  refine eventually_all.2 fun i => ?_
  obtain ⟨c, hc, e⟩ := h i
  simpa only [colMul, e] using ae_family hc

theorem ratCols_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : RatCols d.jX := fun i => by
  refine ⟨fun k => d.e k i, fun h => ?_, fun _ => rfl⟩
  have := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_zero fun k _ => by rw [show d.e k i = 0 from congrFun h k, mul_zero]] at this
  exact zero_ne_one this

theorem ae_colsAt {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {x : Mx D W.rank ρ} (hx : RatCols x) {LV : Lat V}
    {LW : Lat W} (hV : IsSelfDualC V LV) (hW : IsSelfDualC W LW) : ∀ᶠ v : Pl D in cofinite, ColsAt d x LV LW v := by
  filter_upwards [ae_std hV, ae_std hW, GlobalTheory.FinPl.AlmostAll.latA_eq_latV D, (ratCols_jX d).ae, hx.ae] with v h1 h2 h3 h4 h5 i a _
  rw [h3, h1, h2, h4, h5]

theorem ae_primAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {L : Lat S} (h : IsSelfDualC S L) : ∀ᶠ v : Pl D in cofinite, PrimAt ψ d L v := by
  filter_upwards [ae_std h, (ratCols_jX d).ae, GlobalTheory.FinPl.Conductor.eventually_conductor D ψ hψ] with v h1 h2 h3 i j _ s hs
  obtain ⟨ε, -, hε, hid⟩ := exists_idem v
  simp only [h1 _, h2]
  rw [h3 s hs]
  refine ⟨fun h => ?_, fun h a ha => int_mul h ha⟩
  have := h ε hε
  rwa [mul_comm, (hid s).1 hs] at this

theorem incAdj_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (a : AE D) (y : Mx D S.rank ρ) :
    d.incAdj S (a • y) = cA D a • (show Mx D T.rank S.rank from d.incAdj S y) := by
  show d.jY * (incA D (-D.host.xi0⁻¹) • (adj (a • y) * gA S)) = cA D a • (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
  rw [adj_smul, Matrix.smul_mul, smul_comm, Matrix.mul_smul]

theorem incAdj_yZero {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {z : Fin S.rank → D.host.E} (hz : z ≠ 0)
    (hρ : 0 < ρ) : ∃ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, M ≠ 0 ∧ d.incAdj S (yZero S ρ z) = rat M := by
  let y : Matrix (Fin S.rank) (Fin ρ) D.host.E := of fun k i => if i.1 + 1 = ρ then -z k else 0
  have hy : yZero S ρ z = rat y := by
    ext k i
    show -(incA D (z k) * (if i.1 + 1 = ρ then 1 else 0)) = incA D (if i.1 + 1 = ρ then -z k else 0)
    split_ifs
    · rw [mul_one, RingHom.map_neg]
    · rw [mul_zero, neg_zero, RingHom.map_zero]
  refine ⟨d.e' * (-D.host.xi0⁻¹ • (yᴴ * S.gram)), fun h => hz ?_, ?_⟩
  · have h1 : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
    have h2 : -D.host.xi0⁻¹ • (yᴴ * S.gram) = 0 := by
      rw [← Matrix.one_mul (-D.host.xi0⁻¹ • _), ← h1, Matrix.mul_assoc, h, Matrix.mul_zero]
    rw [smul_eq_zero, neg_eq_zero, inv_eq_zero] at h2
    have h3 : yᴴ = 0 := by
      rw [← Matrix.mul_one yᴴ, ← mul_nonsing_inv _ (gram_isUnit_det S), ← Matrix.mul_assoc,
        h2.resolve_left (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D), Matrix.zero_mul]
    funext k
    have h4 := congrFun (congrFun (conjTranspose_eq_zero.1 h3) k) ⟨ρ - 1, by omega⟩
    simpa [y, show ρ - 1 + 1 = ρ by omega] using h4
  · rw [hy, rat_mul, rat_smul, rat_mul, rat_conjTranspose]
    rfl

section Split

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Split

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n]

end Frames

section Ram

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Ram

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.FinPl.Inhab

end
