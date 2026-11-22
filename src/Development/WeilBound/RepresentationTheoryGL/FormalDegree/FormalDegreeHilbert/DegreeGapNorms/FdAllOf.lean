module

public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem fdAll_of (hM : ModelDS) (hF : FdModel) : FdAll := by
  intro n ε lam hl H _ _ σ hσ
  obtain ⟨T⟩ := HW.kType_exists ε lam hl
  obtain ⟨μ, hμ⟩ := S7.exists_mu hl
  have hDS := (hM n ε lam T μ hl hμ).2
  have hd := hF n ε lam T μ hl hμ
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.DSUniq.ds_unique
    CompanionTheory.D.LK.hMultAlg CompanionTheory.D.LK.hKModExists CompanionTheory.D.LK.hOrthCyc
    n ε lam H _ σ (sigLam ε (PsiM T μ) T.w) hl hσ hDS
  have hc : ∀ (v w : H) (g : Formalism.REAL.UJ ε), Formalism.MainNotions.S.coefOn σ v w g =
      Formalism.MainNotions.S.coefOn (sigLam ε (PsiM T μ) T.w) (U v) (U w) g := by
    intro v w g
    simp only [Formalism.MainNotions.S.coefOn]
    rw [← hU _ g.2 v, LinearIsometryEquiv.inner_map_map]
  refine ⟨hd.1, fun v w v' w' => ?_⟩
  obtain ⟨h1, h2⟩ := hd.2 (U v) (U w) (U v') (U w')
  simp only [hc]
  refine ⟨h1, ?_⟩
  rw [h2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

end PositivityTheory.RgFd
