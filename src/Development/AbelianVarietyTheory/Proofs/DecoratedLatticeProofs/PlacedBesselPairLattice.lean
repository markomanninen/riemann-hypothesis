module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBesUnscaledDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntOfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfPsiE

@[expose] public section

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LineIdeal

section Loc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc NumberField GlobalTheory.AdelicU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem int_of_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : Af F ⊗[F] E)
    (h : ∀ w, Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) y ∈ intLoc F E w) :
    y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have hfg : (stdLattice E 1).FG := Submodule.fg_pi fun _ => by
    rw [← Submodule.one_eq_range]; exact Submodule.fg_unit 1
  have h1 : (fun _ : Fin 1 => y) ∈ latHat F E (stdLattice E 1 : Set _) :=
    (mem_latHat_iff hfg _).2 fun w => mem_latLoc_stdLattice.2 fun _ => h w
  generalize hA : AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} = A
  have hA' : ∀ a ∈ intAf F, ∀ x : 𝓞 E, a ⊗ₜ[F] (x : E) ∈ A := fun a ha x => hA ▸ AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩
  have key : latHat F E (stdLattice E 1 : Set _) ≤ A.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => Af F ⊗[F] E) 0) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, x, hx, rfl⟩
    obtain ⟨r, hr⟩ := hx 0 trivial
    change b ⊗ₜ[F] x 0 ∈ A
    rw [← hr]
    exact hA' b hb r
  exact key h1

theorem loc_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : Af F ⊗[F] E)
    (h : y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) (w) :
    Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) y ∈ intLoc F E w := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    exact tmul_mem_intLoc (hb w) x
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem exists_mulVec_iff {R : Type} [CommRing R] {n : ℕ} (M : GL (Fin n) R) (P : (Fin n → R) → Prop) (w : Fin n → R) :
    (∃ x, P x ∧ M.1 *ᵥ x = w) ↔ P ((M⁻¹).1 *ᵥ w) := by
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [← e, mulVec_mulVec, Units.inv_mul, one_mulVec]
  · exact fun H => ⟨_, H, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩

variable {D : D7}

theorem int_iff_loc {v : Pl D} {a : AE D} (ha : a ∈ idAt D (· = v)) :
    a ∈ intAt D (· = v) ↔ compAt D v a ∈ intLoc D.host.F D.host.E v := by
  refine ⟨fun h => loc_of_int _ h.2 v, fun h => ⟨ha, int_of_loc _ fun w => ?_⟩⟩
  by_cases e : w = v
  · subst e; exact h
  · have h0 : compAt D w a = 0 := compAt_of_idAt ha e
    change compAt D w a ∈ _
    rw [h0]
    exact zero_mem _

theorem line_loc (V : HSp D) (Λ : Lat V) (hΛ : Λ.FG) (v : Pl D) (g : GA D V) (y₀ : Fin V.rank → AE D)
    (h : ∀ a ∈ idAt D (· = v), mt V g⁻¹ *ᵥ (a • y₀) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ a ∈ intAt D (· = v))
    (c : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    (∃ x ∈ latLoc D.host.F Λ v, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v g)).1 *ᵥ x =
      c • vecLoc v (finPart D ∘ y₀)) ↔ c ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨a, ha, hc⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (n := 1) v fun _ => c
  have hc' : compAt D v (a 0) = c := congrFun hc 0
  have hs : ∀ i, (a 0 • y₀) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ (ha 0)
  have e : vecLoc v (finPart D ∘ (a 0 • y₀)) = c • vecLoc v (finPart D ∘ y₀) := by
    funext i
    rw [← hc']
    exact map_mul (compAt D v) (a 0) (y₀ i)
  have key : ∀ (g : GA D V) y, vecLoc v (finPart D ∘ (mt V g *ᵥ y)) =
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v g)).1 *ᵥ vecLoc v (finPart D ∘ y) := fun g y => by
    rw [GlobalTheory.FinPl.KOpen.fin_mulVec]
    exact vecLoc_mulVec D.sp.cm.sig V.gram v g _
  rw [← hc', ← int_iff_loc (ha 0), ← h _ (ha 0), hc',
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hΛ v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ _ hs), key, e, map_inv, map_inv]
  exact exists_mulVec_iff _ (· ∈ latLoc D.host.F Λ v) _

end Loc

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos

section Word

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}

theorem xu_fixes (hE : IdE X) (r : Fin D.R.rS) :
    mt (D.sp.Y 0) ((iotaX X h).symm (1, X.xu u)) *ᵥ ratV (fun k => X.ιE (X.eR r (Fin.cast (rank_eq X h) k))) =
      ratV fun k => X.ιE (X.eR r (Fin.cast (rank_eq X h) k)) := by
  have h1 := (GlobalTheory.Core.SBesLevi.transport_fix D X.B.I X.ιE hE h (rank_eq X h) {X.eR r}
    (Formalism.IndefR.RationalEmbedding.iota D ((iotaX X h).symm (1, X.xu u)))).1
  have e : castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D ((iotaX X h).symm (1, X.xu u))) = (1, X.xu u) :=
    (iotaX X h).apply_symm_apply _
  rw [e] at h1
  refine (GlobalTheory.Core.SBesLevi.bridge_fix D _ _).2 (h1 ⟨?_, ?_⟩ _ rfl)
  · exact one_mem _
  · rintro _ rfl
    exact (X.xu_fix u r).1

theorem first_vec (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (B : SBes X h u ψ (D.sp.X 0)) {μ : D.host.E} (hμ : μ ≠ 0)
    (hz : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) (r : Fin D.R.rS) (hr : r.1 = 0) :
    ∃ s : D.host.E, (s = 1 ∨ s = -1) ∧
      ∀ k, B.d.e k r = s * (μ * (X.B.g : D.host.E) ^ D.R.rS) * X.ιE (X.eR r (Fin.cast (rank_eq X h) k)) := by
  obtain ⟨lam, hl, H⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B', -, -, hz', he, -⟩ := H μ B.vA hμ
  have hne : ∀ B : SBes X h u ψ (D.sp.X 0), vecB B.o B.ζ ≠ 0 := fun B e => besVec_ne_zero B (by rw [e, mulVec_zero])
  have h1 := GlobalTheory.FirstVec.first_eq hψ B'.d B.d (funext fun k => (hz' k).trans (hz k).symm) (hne B') (hne B)
    (fun n => (B'.tieN n).trans (B.tieN n).symm)
    (fun n hn => star_injective ((B'.tieψ n hn).trans (B.tieψ n ((B.tieN n).2 ((B'.tieN n).1 hn))).symm)) r hr
  rcases hl with rfl | rfl
  · exact ⟨1, Or.inl rfl, fun k => by rw [h1, he, hr, Nat.sub_zero, one_mul]⟩
  · exact ⟨(-1) ^ D.R.rS, neg_one_pow_eq_or _ _, fun k => by rw [h1, he, hr, Nat.sub_zero, neg_pow]; ring⟩

end Word

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.LineIdeal

end
