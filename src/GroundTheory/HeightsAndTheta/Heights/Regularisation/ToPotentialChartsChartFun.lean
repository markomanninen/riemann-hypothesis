module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

theorem closure_image_subset {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [T2Space Y] (e : OpenPartialHomeomorph X Y) {s : Set X} (hs : closure s ⊆ e.source) :
    IsCompact (e '' closure s) ∧ closure (e.target ∩ e.symm ⁻¹' s) ⊆ e '' closure s := by
  have hK : IsCompact (e '' closure s) :=
    isClosed_closure.isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  refine ⟨hK, closure_minimal ?_ hK.isClosed⟩
  rintro y ⟨hy, hys⟩
  exact ⟨e.symm y, subset_closure hys, e.right_inv hy⟩

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

namespace RegCharts

def ofPotentialCharts [CompactSpace X] (P : PotentialCharts A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) : RegCharts A where
  n := P.N
  ψ := P.chart
  compat := P.compat
  W j := (P.chart j).target
  W' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
  W'' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.inner j
  isOpen_kappaOpenNeighbourhood j := (P.chart j).open_target
  isOpen_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_mid j)
  isOpen_alt_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_inner j)
  W_subset _ := subset_rfl
  isCompact_closure_middle j :=
    (closure_image_subset (P.chart j) (P.closure_mid j)).1.of_isClosed_subset isClosed_closure
      (closure_image_subset (P.chart j) (P.closure_mid j)).2
  closure_W'_subset j := (closure_image_subset (P.chart j) (P.closure_mid j)).2.trans
    (image_subset_iff.2 fun _ hx => (P.chart j).map_source (P.closure_mid j hx))
  closure_W''_subset j := by
    have hs := (P.closure_inner j).trans (P.mid_subset_source j)
    refine (closure_image_subset (P.chart j) hs).2.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(P.chart j).map_source (hs hx), ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rw [(P.chart j).left_inv (hs hx)]
    exact P.closure_inner j hx
  cover x := by
    obtain ⟨j, hj⟩ := P.cover x
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hj)
    refine ⟨j, hs, (P.chart j).map_source hs, ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.inner j
    rw [(P.chart j).left_inv hs]
    exact hj
  θ := P.th
  θ_pot := P.th_pot
  om := om
  om_pot := om_pot
  om_pos := om_pos
  q := P.q
  q_smooth := P.q_smooth
  q_θ j y hy _ := by
    obtain ⟨V, hV, hyV, G, hG, hq⟩ := P.q_th j y y ⟨P.th.mem_U y, hy⟩
    refine ⟨V, hV, hyV, fun x => -G x, fun k => (hG k).neg, fun x hx _ => ?_⟩
    have := hq x hx
    simp only [Complex.neg_re]
    linarith

variable [CompactSpace X] (P : PotentialCharts A) (om : LocPot X) (om_pot : IsPotential A om)
  (om_pos : IsPosPot A om)

end RegCharts

namespace RegCharts

variable (R : RegCharts A)

variable [T2Space X] (hW : ∀ j, R.W j ⊆ ball 0 1)

end RegCharts

section RoundTrip

variable [CompactSpace X] [T2Space X]

end RoundTrip

namespace PotentialCharts

variable (P : PotentialCharts A)


end PotentialCharts

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
