module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Formalism.LocalToGlobal.Columns.RecLevelCls

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.PtDeco

theorem isPtOf_iff_decoRaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), Q = ∅ → (IsPtOf hc g p ↔ g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g p hQ
  subst hQ
  have hlast : ∀ i : Fin n, i.1 + 1 = n → lastIdx n = i := fun i hi => Fin.ext (by simp [lastIdx]; omega)
  constructor
  · intro h
    have hg : g ∈ UAd hc n := h.uni
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by
      have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
        let L := p.deco.1.N
        let W := Submodule.span E (L : Set (Sp E n))
        change W = ⊤
        by_contra hW
        let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
        let f : Sp E n →ₗ[E] Module.Dual E W :=
          (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
        have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt hW
        obtain ⟨x, hx, hx₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
        have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
        have hsmul (a : E) : a • e x ∈ L := by
          rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
          intro y hy
          apply hStd_mem_one_symm
          have hxy : hStd E n (e x) y = 0 :=
            congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
          simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
        let i : E →ₗ[𝓞 E] L :=
          ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
        let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
        let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
          smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
      have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg)
        hspan
      ext v
      conv_lhs => rw [← h1]
      have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
          v ∈ Formalism.UG.CS.globLat x Λ ↔ ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        fun _ _ _ => Iff.rfl
      rw [e1, e1, inv_one, Units.val_one, Matrix.one_mulVec]
      exact h.lat _
    refine ⟨hg, Deco.Ok.ext_on p.deco.2 (decorated_lattice_exists hc n ST SG g hg) hN (fun P x hx => ?_) (fun w x hx => ?_)⟩
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      refine HasRes.unique (h.f P x hx (lastIdx n) (by simp [lastIdx]; have := NeZero.pos n; omega)) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' _)
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      funext i
      refine HasRes.unique (h.be w x hx i) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' i)
  · rintro ⟨hg, hd⟩
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by rw [hd]; rfl
    refine ⟨hg, hN ▸ PtExist.carries_globLat g, fun P x hx i hi => ?_, fun w x hx i => ?_,
      fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx), hlast i hi]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx)]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)

end GlobalTheory.Mem.Col2.PtDeco

end
