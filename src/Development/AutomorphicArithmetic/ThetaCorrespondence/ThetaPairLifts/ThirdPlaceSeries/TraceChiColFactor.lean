module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryClassRelation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
noncomputable section
namespace GlobalTheory.FamTraceChiCol
set_option maxHeartbeats 8000000 in
theorem trace_chi_col_factor_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (y : (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U), (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi y : ℂˣ) : ℂ) * ∏ i : Fin a.n, GlobalTheory.FamTraceChiCol.colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) ((a.pl i).1.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) y.1 = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a y
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg := hA.lev.1
  set w : Fin a.n → IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := fun i => (a.pl i).1.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) with hw
  have hw_mem : ∀ i, (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 0 * (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 1 : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ (w i).asIdeal := by
    intro i
    have h1 := hTP.1 (a.pl i).1 (a.pl i).2
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact h1
  have hw_inj : Function.Injective w := by
    intro i i' hii
    obtain ⟨PP, _, hu⟩ := hTP.2 (w i) (hw_mem i)
    have e1 := hu (a.pl i).1 ⟨(a.pl i).2, rfl⟩
    have e2 := hu (a.pl i').1 ⟨(a.pl i').2, hii.symm⟩
    exact a.pl.injective (Subtype.ext (e1.trans e2.symm))
  set S : Fin 2 → Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) :=
    fun j => {v | ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal} with hS
  have hrange : S 0 ∪ S 1 = Set.range w := by
    ext v
    simp only [Set.mem_union, hS, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro hv
      have hv' : (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 0 * (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 1 : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal := (mem_type_prod_iff v).2 (Fin.exists_fin_two.2 hv)
      obtain ⟨PP, ⟨hPP, hPv⟩, _⟩ := hTP.2 v hv'
      exact ⟨a.pl.symm ⟨PP, hPP⟩, by simp [hw, hPv]⟩
    · rintro ⟨i, rfl⟩
      exact Fin.exists_fin_two.1 ((mem_type_prod_iff (w i)).1 (hw_mem i))
  have hfin : ∀ j, (S j).Finite := fun j =>
    (Set.finite_range w).subset (hrange ▸ (by
      rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> subst hj
      · exact Set.subset_union_left
      · exact Set.subset_union_right))
  have hdisj : Disjoint (S 0) (S 1) := by
    rw [Set.disjoint_left]
    intro v h0 h1
    exact absurd (type_idx_unique (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) h0 h1) (by decide)
  have hinner : ∀ j : Fin 2,
      (∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal),
        (Formalism.L2.Forms.lamJ ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.psi0 j v h) ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.chiB j v h) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.t 0 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k
          (Formalism.L2.Forms.redM (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat j v h ((_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.fr j v h)
            (Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) y.1))))⁻¹) =
      ∏ᶠ v ∈ S j, (colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) v y.1)⁻¹ := by
    intro j
    refine finprod_congr fun v => finprod_congr fun h => ?_
    rw [colLam_eq (_root_.GlobalTheory.MiTop.formsAtZero W u) j h y.1]
  have hchi := (_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.chi_eq y
  rw [Fin.prod_univ_two, hinner 0, hinner 1, ← finprod_mem_union hdisj (hfin 0) (hfin 1), hrange,
    finprod_mem_range hw_inj, finprod_eq_prod_of_fintype] at hchi
  rw [hchi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (colLam_ne_zero (_root_.GlobalTheory.MiTop.formsAtZero W u) _ _)
end GlobalTheory.FamTraceChiCol
end
end
