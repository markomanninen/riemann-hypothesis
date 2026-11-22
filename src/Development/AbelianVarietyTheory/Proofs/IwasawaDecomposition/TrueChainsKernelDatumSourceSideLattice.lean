module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepChartsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainMiddleStageChartsJoinedMemberStatement
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZeroStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeLocalBasisIffUnimodularCompanionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexValueDetShiftMulRatSpanStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLatticeAtClassIffTwistedPolynomialStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.KerLatS

theorem charts_read_step {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (him : i < B.R.m) :
    ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch)
      (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K := by
  classical
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact GlobalTheory.T.exists_charts_reading_step_zero I hOk hPins l Z u a
  · obtain ⟨Ch0, _, chOf0, K0, hK0, -⟩ := GlobalTheory.T.exists_memberStep_charts I hOk hPins l Z u i hi
    obtain ⟨Ch, _, chOf, K, -, hK, -⟩ := GlobalTheory.T.tupleChain_middleStage_charts_joined_member I hOk hPins l Z u a ((I.Q a).image fun P => P.under (𝓞 B.host.F)) i hi
      Ch0 chOf0 K0 h1 him (fun v => Finset.mem_image) hK0
    exact ⟨_, Ch, chOf, K, hK⟩

theorem kerEntHyp_latS : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls i → ((I.rec7 l Z).chTw u μ).Y i → ℂ, (∃ x ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat i).L, ((I.tw l l0 Z).fm u μ).emb i x = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt _hUnf _hJets u μ w hw i hi φ
  obtain ⟨bad, Ch, chOf, K, hK⟩ := charts_read_step I hOk hPins l Z u μ i hi.le hi
  have hY : I.IdY l Z u μ i hi.le (Equiv.refl _) := fun _ => rfl
  have V := GlobalTheory.T.hermitianChart_complex_rational_integral_forms I hOk hPins l Z u μ i hi.le bad Ch chOf K (Equiv.refl _) hK hY
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hrat := (V.rat ((I.fm l u μ).emb i x)).1 ⟨x, rfl⟩
    have hlat := (V.lat w trivial x).1 hx
    refine ⟨hrat.1, fun c => ?_⟩
    obtain ⟨Bm, hBm⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis ((I.rec7 l Z).what₂.places.resChar w) _ _
      ((I.stp u μ i).rep c).1.1.deco.2.lat.fg (by
        open Formalism.HermitianLatticesTheory Module in
        let L := ((I.stp u μ i).rep c).1.1.deco.1.N
        have hL := ((I.stp u μ i).rep c).1.1.deco.2.lat
        have hu : IsUnimodular (Formalism.L2.Col.hStd B.fields.E (B.R.N i)) L :=
          ((I.stp u μ i).rep c).1.1.deco.2.uni
        let W := Submodule.span B.fields.E (L : Set (Sp B.fields.E (B.R.N i)))
        change W = ⊤
        by_contra h
        let e : Sp B.fields.E (B.R.N i) ≃ₗ⋆[B.fields.E] Sp B.fields.E (B.R.N i) := starLinearEquiv B.fields.E
        let g : Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Module.Dual B.fields.E W :=
          (LinearMap.domRestrict' W).comp ((Formalism.L2.Col.hStd B.fields.E (B.R.N i)).comp e.toLinearMap)
        have hdim : finrank B.fields.E (Module.Dual B.fields.E W) <
            finrank B.fields.E (Sp B.fields.E (B.R.N i)) := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt h
        obtain ⟨x, hx, hx₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
        have hsmul (a : B.fields.E) : a • e x ∈ L := by
          rw [← hu, dualBasic_mem_dual]
          intro y hy
          apply hStd_mem_one_symm
          have hxy : Formalism.L2.Col.hStd B.fields.E (B.R.N i) (e x) y = 0 :=
            congrArg (fun f : Module.Dual B.fields.E W => f ⟨y, Submodule.subset_span hy⟩)
              (LinearMap.mem_ker.mp hx)
          simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
        let j : B.fields.E →ₗ[𝓞 B.fields.E] L :=
          ((LinearMap.toSpanSingleton B.fields.E _ (e x)).restrictScalars (𝓞 B.fields.E)).codRestrict L hsmul
        let : Module.Finite (𝓞 B.fields.E) L := Module.Finite.iff_fg.mpr hL.fg
        let : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.Finite.of_injective j fun a b hab =>
          smul_left_injective B.fields.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField B.fields.E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E)))
    have hBm' := (GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion I hOk hPins l Z Y u μ w hw i hi.le c Bm).2 hBm
    exact (GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat.2 c) Bm
      hBm).1 (hlat c Bm hBm')
  · rintro ⟨hFi, hc⟩
    have hrat : ∀ c, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, φ c z =
        fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P
          ((Equiv.refl _) z) := by
      intro c
      obtain ⟨v, hv, -⟩ := hc c
      rw [← hv]
      exact GlobalTheory.T.complexValue_det_shift_mul_ratSpan I hOk hPins l Z Y O hQp hStd u μ i hi (Equiv.refl _) hY v
    obtain ⟨x, hx⟩ := (V.rat φ).2 ⟨hFi, hrat⟩
    refine ⟨x, (V.lat w trivial x).2 fun c Bm hBm => ?_, hx⟩
    have hBm' := (GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion I hOk hPins l Z Y u μ w hw i hi.le c Bm).1 hBm
    have h1 := (GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat c) Bm
      hBm').2 (hc c)
    rw [hx]
    exact h1

end GlobalTheory.KerLatS
