module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals

@[expose] public section

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}



omit [StarRing E] in
theorem exists_coprime_mem (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ Q ∈ S, ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal) : ∃ a : ℕ, a.Coprime p ∧ ∀ Q ∈ S, ((a : ℕ) : 𝓞 E) ∈ Q.asIdeal := by
  classical
  have h1 : ∀ Q : S, ∃ a : ℕ, a.Coprime p ∧ ((a : ℕ) : 𝓞 E) ∈ Q.1.asIdeal := by
    intro Q
    haveI := Q.1.isMaximal
    haveI : Finite (𝓞 E ⧸ Q.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.1.ne_bot
    letI := Ideal.Quotient.field Q.1.asIdeal
    have hp : (ringChar (𝓞 E ⧸ Q.1.asIdeal)).Prime := CharP.prime_ringChar _
    refine ⟨_, (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hS Q.1 Q.2 ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 h
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 dvd_rfl
  choose a ha ha' using h1
  refine ⟨∏ Q, a Q, Nat.Coprime.prod_left fun Q _ => ha Q, fun Q hQ => ?_⟩
  exact Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem a (Finset.mem_univ ⟨Q, hQ⟩))) (ha' ⟨Q, hQ⟩)

end Deco

section Coef

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K)

theorem natCast_notMem_of_coprime {a p : ℕ} (h : a.Coprime p) (w : HeightOneSpectrum (𝓞 K))
    (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  obtain ⟨x, y, e⟩ := (Nat.Coprime.cast (R := 𝓞 K) h)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ ha) (w.asIdeal.mul_mem_left _ hw)))

omit [Fintype ι] in
theorem nsmul_mem_tauLat (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    {y : Fin n → K} (hy : y ∈ tauLat emb τ L) : a • y ∈ tauLat emb τ L' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a • x, h x hx, ?_⟩
    funext i
    simp
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

omit [Fintype ι] in
theorem localization_dualFr_tauLat_le (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (dualFr (tauLat emb τ L')) ≤ localization₂ w.asIdeal (dualFr (tauLat emb τ L)) := by
  refine GlobalTheory.TransLoc.localization_le_of_smul_mem w ha fun φ hφ x hx => ?_
  have := hφ _ (nsmul_mem_tauLat emb τ h hx)
  rw [dotProduct_smul] at this
  rw [smul_dotProduct, Nat.cast_smul_eq_nsmul]
  exact this

theorem localization_nabK_delK_congr (lam : ι → DomWeight n) {M M' : ι → Submodule (𝓞 K) (Fin n → K)}
    (hM : ∀ τ, Submodule.IsFullLattice K (M τ)) (hM' : ∀ τ, Submodule.IsFullLattice K (M' τ)) (w : HeightOneSpectrum (𝓞 K))
    (h : ∀ τ, localization₂ w.asIdeal (M τ) = localization₂ w.asIdeal (M' τ)) :
    localization₂ w.asIdeal (nabK lam M) = localization₂ w.asIdeal (nabK lam M') ∧
      localization₂ w.asIdeal (delK lam M) = localization₂ w.asIdeal (delK lam M') := by
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have hB' : ∀ τ, IsBasisAt w (M' τ) (B τ) := fun τ => (h τ).symm.trans (hB τ)
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have h2 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M' hM' w B hB'
  have key : ∀ (T : Submodule (𝓞 K) (Pol K ι n)) (x : VV K lam),
      x ∈ localization₂ w.asIdeal (T.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔ x.1 ∈ localization₂ w.asIdeal T := by
    intro T x
    exact Iff.rfl
  constructor
  · ext x
    unfold nabK
    rw [key, key, h1.1, h2.1]
  · ext x
    unfold delK
    rw [key, key, h1.2, h2.2]

theorem localization_nabAtr_delAtr_congr (lam : ι → DomWeight n) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsFullLattice E L) (hL' : Submodule.IsFullLattice E L') {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (h' : ∀ x ∈ L', a • x ∈ L) (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr emb lam L) = localization₂ w.asIdeal (nabAtr emb lam L') ∧
      localization₂ w.asIdeal (delAtr emb lam L) = localization₂ w.asIdeal (delAtr emb lam L') :=
  localization_nabK_delK_congr lam
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L' hL')) w
    fun τ => le_antisymm (localization_dualFr_tauLat_le emb τ h' w ha) (localization_dualFr_tauLat_le emb τ h w ha)

end Coef

variable {p : ℕ} {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem use₃ (lam : X.Tau → DomWeight n) (hT : ∀ Q ∈ ST, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal)
    (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (nabAtr X.emb lam d.1.N) ∧
      localization₂ w.asIdeal (delAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (delAtr X.emb lam d.1.N) := by
  obtain ⟨a, hap, ha⟩ := exists_coprime_mem p ST hT
  letI : Submodule.IsFullLattice X.E d.1.N := Formalism.L2.Ker.full_of_sd ⟨d.2.lat, d.2.uni⟩
  letI := d.2.Lsh_lattice
  have hLsh : Submodule.IsFullLattice X.E d.1.Lsh := Submodule.IsFullLattice.of_le X.E d.2.N_le_Lsh
  refine localization_nabAtr_delAtr_congr X.emb lam hLsh inferInstance (a := a) (fun x hx => ?_)
    (fun x hx => Submodule.smul_of_tower_mem _ a (d.2.N_le_Lsh hx)) w (natCast_notMem_of_coprime hap w hw)
  rw [← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
  exact d.2.smul_Lsh_mem_N (fun P => by rw [map_natCast]; exact ha P.1 P.2) hx

end GlobalTheory.GO
