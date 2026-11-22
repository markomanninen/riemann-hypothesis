module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolume
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotentStatement

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.Rodier.RadInt
open MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
variable {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}
variable [MeasurableSpace (unipU k d hd)] [BorelSpace (unipU k d hd)]
private theorem phi_levi_current (ψ : AddChar k Circle) (f f' : IndSp (stdBlocks d hd) ρ) (a : GL (Fin N) k)
    (ha : a ∈ unipL k d hd) (m : unipM k d)
    (hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1)
    (hf' : f' = parInd (stdBlocks d hd) ρ a f) :
    phi ψ f' = fun x => ρ m.1 (phi ψ f (conjU a⁻¹ (inv_mem (unipL_le ha)) x)) := by
  subst hf'
  funext x
  have e1 : pm k (wOpen d hd) * x.1 * a = leviEmb k (stdBlocks d hd) m.1 *
      (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1) := by
    rw [← hm]
    show _ = pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ * (pm k (wOpen d hd) * (a⁻¹ * x.1 * a⁻¹⁻¹))
    group
  have e2 := parInd_law (stdBlocks d hd) ρ f
    ⟨leviEmb k (stdBlocks d hd) m.1, leviEmb_mem_parab k (stdBlocks d hd) m.1⟩
    (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1)
  rw [leviProj_leviEmb, deltaHalf_unipM m, Units.val_one, one_smul] at e2
  show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • (parInd (stdBlocks d hd) ρ a f).1.1 (pm k (wOpen d hd) * x.1) =
    ρ m.1 ((((thetaU ψ (conjU a⁻¹ (inv_mem (unipL_le ha)) x))⁻¹ : ℂˣ) : ℂ) •
      f.1.1 (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1))
  rw [parInd_apply, e1, thetaU_conjU, map_smul]
  exact congrArg _ e2

private theorem radInt_levi_current {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd))
    [μ.IsHaarMeasure] (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d)
    (hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1)
    (f f' : openFns d hd ρ) (hf : (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f) :
    radInt hψ hρ μ f' = ρ m.1 (radInt hψ hρ μ f) := by
  have key := smInt_comp μ (ρ m.1) (conjU a⁻¹ (inv_mem (unipL_le ha))) (phi ψ f.1)
    (measurePreserving_conjU μ _ _) (isLocallyConstant_phi hψ _) (hasCompactSupport_phi ψ hρ _ f.2)
  show smInt μ (phi ψ f'.1) = _
  rw [phi_levi_current ψ f.1 f'.1 a ha m hm hf, key]
  rfl

end GlobalTheory.CompanionTheory.Rodier.RadInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_jacquet_integral_volume : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ), (∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ), (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f) ∧ (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d), pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 → ∀ f f' : openFns d hd ρ, (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f → J f' = ρ m.1 (J f)) ∧ ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) → (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) → 0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W), (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) → (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ
  letI : MeasurableSpace (unipU k d hd) := borel _
  haveI : BorelSpace (unipU k d hd) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipU k d hd) :=
    (RadInt.isClosed_unipU (k := k) (d := d) (hd := hd)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : MeasureTheory.Measure (unipU k d hd) := MeasureTheory.Measure.haar
  exact ⟨RadInt.radInt hψ hρ μ, RadInt.volU μ,
    fun u hu hb f f' hf => RadInt.radInt_right hψ hρ μ u hu hb f f' hf,
    fun a ha m hm f f' hf => RadInt.radInt_levi_current hψ hρ μ a ha m hm f f' hf,
    fun L₀ h1 h2 h3 => RadInt.radInt_indicator hψ hρ μ L₀ h1 h2 h3⟩
