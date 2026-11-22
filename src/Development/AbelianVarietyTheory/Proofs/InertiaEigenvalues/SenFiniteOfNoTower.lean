module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongruenceFiltrationGaloisRepStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteImageOfTrivialOnOpenStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongrFiltrationDetectingCharactersCoboundaryStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.PMon.Ram

theorem senFinite_of_noTower (hNT : NoTower) : SenFinite := by
  intro l _ n _ _ K ρ hc M hM
  obtain ⟨N, hN, hanti, hopen, hpow, hroot, hker⟩ := GlobalTheory.T.exists_congruenceFiltration_galoisRep l n K ρ hc
  have hdet := GlobalTheory.T.exists_detecting_characters_congr_filtration l n K ρ M hM N hN
  obtain ⟨k, hk⟩ := hNT l K N hanti hopen hpow hroot hdet
  refine GlobalTheory.T.finite_image_of_trivial_on_inf_isOpen l K (GL n ℚ_[l]) ρ (IK K) (N k) (hopen k) ?_
  intro g hgI hgN
  exact hker g (fun j => hk j ⟨hgI, hgN⟩)

end GlobalTheory.PMon.Ram
