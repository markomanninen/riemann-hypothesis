module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem exists_qkPt_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (ev : M → (TFK (R := V) F ⟶ P.A.A)), (∀ a b, ev (a + b) = ev a * ev b) → (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ (letI := H.starRing; P.oA.act o : P.A.A ⟶ P.A.A)) → (∀ a, ev a ^ N = 1) → (∀ u, u ^ N = 1 → ∃ a, ev a = u) → ∃ pt : M → QkPt P.D.toPre F N, (∀ a, P.ToA F N (pt a) (ev a)) ∧ ∀ (n : ℕ) (z : Fin n → M), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ a : P.D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, a = u + N • t := by
  intro E _ _ _ H V _ _ _ _ hc G P hT F _ _ _ N hN M _ _ ev hadd hsm hpow hsurj
  letI := H.starRing
  open GlobalTheory.TorusExt in
  obtain ⟨f, hto, hon, heq, hfa, hfs, -⟩ := hT F N hN
  have hB := P.D.tau_bimult
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  letI := GlobalTheory.TorusExt.gtGroup P.D.toPre F
  let iotaLocal : P.D.toPre.X →+ GtPtF P.D.toPre F := AddMonoidHom.mk'
    (fun x => (GlobalTheory.TorusExt.exists_iota (F := F) hB x).choose) (by
      intro x x'
      obtain ⟨b, v⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB x).choose_spec
      obtain ⟨b', v'⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB x').choose_spec
      obtain ⟨b'', v''⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
      refine (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ((GlobalTheory.TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
      have sym01 (a b c : TF (R := V) F ⟶ P.D.toPre.P.A) :
          th P.D.toPre y J a b c = th P.D.toPre y J b a c := by
        have e := (val_corr hJ P.D.toPre.cub.cubeSymmetric_swap_first (lift a (lift b c)).left).trans
          (val_cub P.D.toPre.cub (lift a (lift b c)) hJ _ _ _)
        refine e.trans ?_
        congr 1 <;> simp [x3]
      have sym12 (a b c : TF (R := V) F ⟶ P.D.toPre.P.A) :
          th P.D.toPre y J a b c = th P.D.toPre y J a c b := by
        have e := (val_corr hJ P.D.toPre.cub.cubeSymmetric_swap_last (lift a (lift b c)).left).trans
          (val_cub P.D.toPre.cub (lift a (lift b c)) hJ _ _ _)
        refine e.trans ?_
        congr 1 <;> simp [x3]
      rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', sym01, sym12]
      exact tau_mul (𝟙 (TF (R := V) F)) hJ hB x x' χ)
  have hi (x : P.D.toPre.X) : GtPtF.IsIota x (iotaLocal x) := (GlobalTheory.TorusExt.exists_iota hB x).choose_spec
  have hn (p : QkPt P.D.toPre F N) : N • p.g = iotaLocal p.y := by
    obtain ⟨h, hn, hi'⟩ := p.eq
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn).symm.trans (GlobalTheory.TorusExt.isIota_unique hi' (hi p.y))
  choose pt hpt using fun a => hon (ev a) (hpow a)
  refine ⟨pt, fun a => (hto _ _).2 (hpt a).symm, fun n z hz y => ?_⟩
  have yadd : ∀ a b, ∃ t : P.D.toPre.X, (pt (a + b)).y = (pt a).y + (pt b).y + N • t := fun a b => by
    let q : QkPt P.D.toPre F N := ⟨(pt a).y + (pt b).y, (pt a).g + (pt b).g,
      iotaLocal ((pt a).y + (pt b).y), (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
        rw [nsmul_add, hn, hn, map_add]), hi _⟩
    have e := hfa _ _ _ (show QkAdd (pt a) (pt b) q from
      ⟨q, rfl, (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB q⟩)
    rw [hpt, hpt, ← hadd, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, ht⟩
  have ysm : ∀ (o : 𝓞 E) a, ∃ t : P.D.toPre.X, (pt (o • a)).y = o • (pt a).y + N • t := fun o a => by
    obtain ⟨q, hq⟩ := qkAct_exists hG hB P.oD o (pt a)
    obtain ⟨r, hr, hact, he⟩ := hq
    have e := hfs _ _ _ (show QkAct P.oD o (pt a) r from ⟨r, hr, hact, qk_equiv_refl hB r⟩)
    rw [hpt, ← hsm, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, by simpa [hr] using ht⟩
  have key : ∀ m ∈ Submodule.span (𝓞 E) (Set.range z),
      ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, (pt m).y = u + N • t := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨b, rfl⟩, 0, by rw [smul_zero, add_zero]⟩
    | zero =>
      obtain ⟨t, ht⟩ := ysm 0 0
      rw [zero_smul, zero_smul] at ht
      exact ⟨0, Submodule.zero_mem _, t, ht⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨u', hu', t', ht'⟩ := hb
      obtain ⟨s, hs⟩ := yadd a b
      exact ⟨u + u', Submodule.add_mem _ hu hu', t + t' + s, by
        rw [hs, ht, ht', smul_add, smul_add]; abel⟩
    | smul o a _ ha =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨s, hs⟩ := ysm o a
      exact ⟨o • u, Submodule.smul_mem _ o hu, o • t + s, by
        rw [hs, ht, smul_add, smul_add, smul_comm o N t, add_assoc]⟩
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨g, hg⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V _ hA P.D F).2.1 N hN
    (iotaLocal y)
  let p : QkPt P.D.toPre F N :=
    ⟨y, g, iotaLocal y, hg, hi y⟩
  have hp : f p ^ N = 1 := by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((hto p _).2 rfl w hw).1
  obtain ⟨m, hm⟩ := hsurj _ hp
  obtain ⟨s, hs, -⟩ := (heq (pt m) p).1 ((hpt m).trans hm)
  obtain ⟨u, hu, t, ht⟩ := key m (hz ▸ Submodule.mem_top)
  refine ⟨u, hu, t + s, ?_⟩
  have hs' : y = (pt m).y + N • s := hs
  rw [hs', ht, smul_add, add_assoc]

end GlobalTheory.EtaVal
