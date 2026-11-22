module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedExtensionOfSeriesPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidifiedExtension_of_series_pair : ∀ (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  first | exact @GlobalTheory.Katz.exists_rigMap | exact GlobalTheory.Katz.exists_rigMap | (intros; apply GlobalTheory.Katz.exists_rigMap <;> assumption)
