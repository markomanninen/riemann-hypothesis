module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroSmulMem

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.BSpan

theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem ..)

theorem smul_mem_of_dvd {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] {M : Submodule A V} {a b : A} {x : V}
    (hab : a ∣ b) (hx : a • x ∈ M) : b • x ∈ M := by
  obtain ⟨c, rfl⟩ := hab
  rw [mul_comm, mul_smul]
  exact M.smul_mem _ hx

theorem dualFr_isFullLattice {K : Type} [Field K] [NumberField K] {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K))
    (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (dualFr M) :=
  GlobalTheory.DualLat.isLattice_dualFr M hM


theorem isLattice_delAtr {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (delAtr emb lam L) :=
  (GlobalTheory.TransLattice.nabDelLattice K ι n lam _ fun τ =>
    dualFr_isFullLattice _ (GlobalTheory.TauLat.tauLat_lattice_dual_round.1 E K ι n emb τ L hL)).2

theorem span_locW_eq_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (Pl : Rows.Places K) (w : Pl.Pl) (M : Submodule (𝓞 K) V)
    (h : ∀ x : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M) : Submodule.span K (locW Pl w M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨d, hd, hx⟩ := h x
  have hd' : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd
  have : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
    rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span hx))

theorem exists_smul_mem_latOf {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok)
    [Finite S.Cl] (M : S.Cl → Submodule (𝓞 K) (VV K lam)) (hM : ∀ c, Submodule.span K (M c : Set (VV K lam)) = ⊤)
    (x : S.FormsK emb lam h) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ S.latOf emb lam h M := by
  classical
  haveI := Fintype.ofFinite S.Cl
  have h1 : ∀ c, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x.1 c ∈ M c := fun c => exists_smul_mem (by rw [hM c]; trivial)
  choose d hd hdM using h1
  refine ⟨∏ c, d c, Finset.prod_ne_zero_iff.2 fun c _ => hd c, fun c => ?_⟩
  exact smul_mem_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ c)) (hdM c)


set_option maxHeartbeats 800000 in
theorem span_locW_BLat : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Pl : Rows.Places K) i (hF : ((I.S i).fam emb (lamT hc i)).Ok) (w : Pl.Pl) P, Submodule.span K (locW Pl w (BLat J emb hc i hF P) : Set ((I.S i).hlat emb (lamT hc i) hF).V) = ⊤ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ hI hJ Pl i hF w P
  haveI := (hI.step i).fin_orb
  refine span_locW_eq_top Pl w _ fun x => ?_
  exact exists_smul_mem_latOf (I.S i) emb (lamT hc i) hF _
    (fun c => by
      let b := c.1
      let d := (I.S i).rep c
      have hd := (hJ.tied i).ok b d
      have hker : Submodule.IsFullLattice E ((J.A i).ker b d P) := by
        letI := (hJ.lev i).ker_lat b d P
        letI := (hJ.lev i).N_lat b d
        refine { span_eq_top := top_unique ?_ }
        rw [← (Submodule.IsFullLattice.span_eq_top (A := E) (M := (J.A i).N b d)), Submodule.span_le]
        intro x hx
        obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.1.ne_bot
        have hrx : r • x ∈ (J.A i).ker b d P := by
          rw [(hJ.tied i).ker_eq]
          exact Submodule.subset_span ⟨hd.N_le_Lsh (Submodule.smul_mem _ r hx),
            ((hd.mem_kerAt P _).1 (hd.smul_mem_kerAt P hr hx)).2⟩
        have hrE : algebraMap (𝓞 E) E r ≠ 0 := by simpa using hr0
        have hspan : r • x ∈ Submodule.span E (((J.A i).ker b d P) : Set _) :=
          Submodule.subset_span hrx
        have hh : (algebraMap (𝓞 E) E r)⁻¹ • (r • x) ∈
            Submodule.span E (((J.A i).ker b d P) : Set _) := Submodule.smul_mem _ _ hspan
        rw [← algebraMap_smul E r x, smul_smul, inv_mul_cancel₀ hrE, one_smul] at hh
        exact hh
      letI := isLattice_delAtr emb (lamT hc i) ((J.A i).ker b d P) hker
      exact Submodule.IsFullLattice.span_eq_top) x

end GlobalTheory.Mem.BSpan
