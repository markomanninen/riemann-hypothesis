module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatch
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.ExistsIsAlgebraicRatFuncFractionRingDedekind

@[expose] public section

open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CharOfLowK

theorem charOfAlgDS : CompanionTheory.RgExh.Fin.CharOfAlgDS := by
  intro n ε V _ _ E hE χ s mu hU hLF hSC hDS
  obtain ⟨hHC, -, hMin, v, hv0, hKH⟩ := hDS
  obtain ⟨S, hSfin, hSK, hvS⟩ := hLF v
  have hU' : Formalism.REAL.IsUnitary (ε ∘ s) (fun a b => E (s a) (s b)) := fun a b x y => hU (s a) (s b) x y
  have hSK' : CompanionTheory.D.DSIC.KStab (ε ∘ s) (fun a b => E (s a) (s b)) S :=
    fun a b hab w hw => hSK (s a) (s b) hab w hw
  have hcap : ∀ Y, Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    have h1 := CompanionTheory.D.DSIC.hAlgCore n (ε ∘ s) mu V (fun a b => E (s a) (s b)) v S hHC
      (GlobalTheory.CompanionTheory.HolCoef.CapLW.glRel_perm hE s) hU' hKH hSfin hSK' hvS hMin Y
    rw [GlobalTheory.CompanionTheory.HolCoef.CapLW.qdet_perm hE s] at h1
    have h2 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • 1 := hSC Y
    have h3 : Formalism.QuantumDeterminants.capP χ Y • v = Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y • v := by
      rw [← h1, h2]
      simp
    exact (smul_left_injective ℂ hv0 h3).symm
  exact exists_perm_of_capelliPolynomial_eq (fun a => (mu a : ℂ)) χ hcap

end GlobalTheory.CompanionTheory.CharOfLowK
