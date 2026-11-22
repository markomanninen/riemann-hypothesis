module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.TowerCodimensionTwo
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG PositivityTheory.ThKF

variable {n d : ℕ} {X X₂ : Spc F E n} {W W₂ : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}


variable (M X₂ W₂) in
def reM : Model σ (reS X X₂) (reS W W₂) := ⟨M.co, M.vac, M.μ, M.dom⟩

theorem so_re : M.So B.ψ B.τ₁ ≤ (reM X₂ W₂ M).So B.ψ B.τ₁ := Submodule.span_mono (by
  rintro _ ⟨f, φ, h1, h2, ⟨h3, ι, h4, h5⟩, rfl⟩
  exact ⟨f, φ, h1, h2, ⟨h3, ι, ⟨h4.bij, h4.trans, h4.mult⟩, h5⟩, rfl⟩)

theorem move (hA : ArchOp) (hM : CartanMove) (hp : IsPair B M χX χW om r s r' s') (hp₂ : IsPair B (reM X₂ W₂ M) χX χW om r s r' s')
    {h : UA σ W.J} (hh : h ∈ UAt σ W (evI F))
    (hθ : ∀ w, (mat h).map (piInf (B.emb w)) * W₂.θ w = W.θ w * (mat h).map (piInf (B.emb w))) :
    ∃ g : UA σ X.J, ∀ Φ ∈ PolData B M, om (g, h⁻¹) Φ ∈ PolData B (reM X₂ W₂ M) := by
  obtain ⟨g, hg, -, hT⟩ := hM F E σ B n d X W M χX χW om r s r' s' hp X₂ W₂ (reM X₂ W₂ M) rfl hp₂ h hh hθ
  obtain ⟨T, h1, -⟩ := hA F E σ B n d X W M χX χW om r s r' s' hp g hg h hh
  refine ⟨g⁻¹, fun Φ hΦ => (Submodule.span_le (p := (PolData B (reM X₂ W₂ M)).comap (om (g⁻¹, h⁻¹)))).2 ?_ hΦ⟩
  rintro _ ⟨f, hf, φ, h2, h3, rfl⟩
  rw [← hT T h1] at hf
  obtain ⟨f₂, h4, rfl⟩ := hf
  obtain ⟨ψ, h5, h6⟩ := pure_eq_pureA hp.good φ h2 h3
  refine Submodule.subset_span ⟨f₂, h4, φ, h2, h3, ?_⟩
  rw [h6, h6]
  change om _ (pureA F (T f₂) ψ) = _
  rw [← h1.1 f₂ ψ h5, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk, map_one,
    Module.End.one_apply]

theorem I_both (hI : PositivityTheory.ThKEst.IInv) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (g : UA σ X.J)
    (h : UA σ W.J) : M.I om (om (g, h) Φ) = fun x => M.I om Φ (x * h) := by
  rw [← I_trans, ← (hI F E σ B n d X W M χX χW om r s r' s' hp _ (hp.weil.isUSplitting.pres (1, h) _ hΦ)).2.1 g,
    ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem sigRe_of (hA : ArchOp) (hM : CartanMove) (hC : CartanConj) (hI : PositivityTheory.ThKEst.IInv) (hS : PositivityTheory.ThKCT.SoStab) : SigRe := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t V V' W t₂
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m)
      (h' : ResEtaPow K χ' n) (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have pairV {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
      IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      res_div h.chars.resβ h.chars.resα rfl, h.weil⟩
  have pairV' {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
      IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      res_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩
  have polData_le {n d : ℕ} {Y : Spc F E n} {Z : Spc F E d} {M : Model σ Y Z}
      (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, h1, h2, rfl⟩
    obtain ⟨u, hu, e⟩ := pure_eq_pureA hM φ h1 h2
    rw [e]
    exact pureA_mem f hu
  obtain ⟨h, hh, hθ⟩ := hC F E σ B _ G.W W _ _ t.base t.geo.hW t₂.geo.hW
  obtain ⟨g, hg⟩ := move (X₂ := V) hA hM (pairV t) (pairV t₂) hh hθ
  obtain ⟨g', hg'⟩ := move (X₂ := V') hA hM (pairV' t) (pairV' t₂) hh hθ
  refine ⟨h⁻¹, ?_⟩
  rintro _ ⟨Φ, hΦ, Φ', hΦ', rfl⟩
  refine ⟨_, hg Φ hΦ, _, ⟨hg' Φ' hΦ'.1, so_re (hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ _ hΦ'.2)⟩, ?_⟩
  change _ = G.M.I om (om (g, h⁻¹) Φ) - G.M'.I om' (om' (g', h⁻¹) Φ')
  rw [I_both hI (pairV t) (polData_le t.geo.hM hΦ), I_both hI (pairV' t) (polData_le t.geo.hM' hΦ'.1)]
  rfl

end PositivityTheory.ThKEnd.Grp

end
