module

public import Formalism.LocalToGlobal.Columns.DilYStab
public import Formalism.LocalToGlobal.Columns.HeckeSpCount
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
public import Formalism.LocalToGlobal.Columns.WithTopLevGTop
public import Formalism.LocalToGlobal.Columns.StabMapRLInjective

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

def frameOfY {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs)) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  Classical.choose (exists_frameD P (hcnt_isFullLattice_of_unimodular d.2.lat d.2.uni))

theorem frameOfY_spec {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs)) :
    ∀ x, frameOfY u P d x ∈ localization₂ P.asIdeal d.1.N ↔ x ∈ stdAt X.E n P :=
  Classical.choose_spec (exists_frameD P (hcnt_isFullLattice_of_unimodular d.2.lat d.2.uni))

variable (hm : R.m = m2 + 2)

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm}

end Top

end Formalism.L2.Col
