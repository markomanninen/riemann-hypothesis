module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDimLeAddMulSectionsDimCutStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorseInequalityArithStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_sec_of_ample_sub_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hp d hd L B M hL hB hM e hlt
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  obtain ⟨s, hs⟩ := IsGenerated.exists_mono_cutHom k (GlobalTheory.structureModule X) hB
  set G := cut (GlobalTheory.structureModule X) hB.isLB s with hG
  haveI : IsFiniteQC G := isFiniteQC_cut (GlobalTheory.structureModule X) hB.isLB s
  obtain ⟨t, ht⟩ := IsGenerated.exists_mono_cutHom k G hB
  have hGd : suppDim G ≤ (d : ℕ) := suppDim_cut_le _ hB.isLB s hsd
  have hcut := interNum_cons_eq_interNum_cut hB.isLB s (P := fun _ : Fin d => L) (fun _ => hL.isLB) hfin
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp (d + 1) (GlobalTheory.structureModule X) hsd L hL
  obtain ⟨C', m₁, hC'⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp d G hGd L hL
  rw [hcut] at hlt
  obtain ⟨m, hm1, hm⟩ := GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds d (topSelfIntersection k L (d + 1)) (interNum k G (fun _ : Fin d => L))
    (fun m => hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0)
    (fun m => hdim k (twist G (lbPow L m)) 0) C C' m₀ m₁ hC hC' hlt
  have hcl : cls (lbPow L m) (isLB_lbPow hL.isLB m) =
      cls (lbPow M m) (isLB_lbPow hM m) + m • cls B hB.isLB := by
    rw [cls_lbPow hL.isLB, cls_lbPow hM, e, smul_add]
  have hmono : ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB),
      cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls M' hM' + j • cls B hB.isLB →
      hdim k (twist G M') 0 ≤ hdim k (twist G (lbPow L m)) 0 := by
    intro j
    induction j with
    | zero =>
      intro M' hM' h
      rw [zero_nsmul, add_zero] at h
      obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq G (isLB_lbPow hL.isLB m) hM' h
      exact (hdim_congr k 0 e).ge
    | succ j ih =>
      intro M' hM' h
      have h1 := cls_tens hM' hB.isLB (isLB_tens hM' hB.isLB)
      have h2 := ih _ (isLB_tens hM' hB.isLB) (by rw [h1, h, succ_nsmul']; abel)
      exact ((GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp G B _ M' hB.isLB _ hM' t ht h1).2.2).trans h2
  have hch : ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB),
      cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls M' hM' + j • cls B hB.isLB →
      hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
        hdim k (twist (GlobalTheory.structureModule X) M') 0 + j * hdim k (twist G (lbPow L m)) 0 := by
    intro j
    induction j with
    | zero =>
      intro M' hM' h
      rw [zero_nsmul, add_zero] at h
      obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_lbPow hL.isLB m) hM' h
      rw [hdim_congr k 0 e]
      omega
    | succ j ih =>
      intro M' hM' h
      have h1 := cls_tens hM' hB.isLB (isLB_tens hM' hB.isLB)
      have h0 : cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls (tens M' B) (isLB_tens hM' hB.isLB) + j • cls B hB.isLB := by
        rw [h1, h, succ_nsmul']; abel
      have h2 := ih _ (isLB_tens hM' hB.isLB) h0
      have h3 := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp (GlobalTheory.structureModule X) B _ M' hB.isLB _ hM' s hs h1).1 0
      change hdim k (twist (GlobalTheory.structureModule X) (tens M' B)) 0 ≤
        hdim k (twist (GlobalTheory.structureModule X) M') 0 + hdim k (twist G (tens M' B)) 0 at h3
      have h4 := hmono j _ (isLB_tens hM' hB.isLB) h0
      rw [Nat.succ_mul]
      omega
  have hch' : hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
      hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0 + m * hdim k (twist G (lbPow L m)) 0 := hch m (lbPow M m) (isLB_lbPow hM m) hcl
  refine ⟨m, hm1, lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) ?_⟩
  show 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0
  have : m * hdim k (twist G (lbPow L m)) 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 := hm
  omega

end GlobalTheory
