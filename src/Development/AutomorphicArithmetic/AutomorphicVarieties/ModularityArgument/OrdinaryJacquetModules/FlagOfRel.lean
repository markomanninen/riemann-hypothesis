module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.FlagJ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.RegArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

private theorem flag_of_rel {K H : Type} [Field K] [Group H] {n : ℕ} (r : H →* GL (Fin n) K) (ψ : Fin n → H →* Kˣ)
    (h0 : ∀ g : Fin n → H, (List.ofFn fun i => ((r (g i) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      algebraMap K _ ((ψ i (g i) : Kˣ) : K)).prod = 0)
    (hch : ∀ t, (W.mat r t).charpoly = ∏ i, (X - C ((ψ i t : Kˣ) : K)))
    (s : H) (hs : Function.Injective fun i => ψ i s) : W.HasFlag r ψ := by
  classical
  let z : MonoidAlgebra K H := MonoidAlgebra.of K H s
  have hlz : ∀ i, MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z = ((ψ i s : Kˣ) : K) := fun i => by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hPz : MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z = W.mat r s := by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hext := AlgebraTools.ord_ext (R := K) ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp r)
    (fun i => (Units.coeHom K).comp (ψ i)) h0
  have hz : ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z -
      MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ j)) z) := fun i j hij => by
    rw [hlz, hlz]
    exact (sub_ne_zero.2 fun e => hij (hs (Units.ext e))).isUnit
  obtain ⟨hc, hlow, hdiag⟩ := AlgebraTools.lag_triangular
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i))) z hext hz
  have hne := AlgebraTools.lag_ne_zero (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) hz (by
      rw [hPz, hch, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hlz]
      simp)
  obtain ⟨g, hg⟩ := AlgebraTools.coi_conj_single _ hc hne
  refine ⟨g, fun t => ?_⟩
  set f := AlgebraTools.lag (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) with hf
  have ent : ∀ (M : Matrix (Fin n) (Fin n) K) a b,
      (Matrix.single a a (1 : K) * M * Matrix.single b b (1 : K) : Matrix (Fin n) (Fin n) K) a b = M a b := fun M a b => by
    simp
  have key : ∀ a b, (g * r t * g⁻¹ : GL (Fin n) K) a b =
      ((g : Matrix (Fin n) (Fin n) K) * (f a * (r t : Matrix (Fin n) (Fin n) K) * f b) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a b := by
    intro a b
    rw [← ent ((g * r t * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b, ← hg a, ← hg b]
    simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h := hlow (MonoidAlgebra.of K H t) i j hji
    rw [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f j = 0 := h
    rw [key, h']
    simp
  · have h := hdiag (MonoidAlgebra.of K H t) i
    simp only [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f i = (ψ i t : K) • f i := h
    rw [key, h', Matrix.mul_smul, Matrix.smul_mul, hg i]
    simp

private theorem chi_single {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem descend {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Ws.Eb.Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Ws.Eb.Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have rep_single {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B] (g : T) (r : B) :
      W.GDet.repAlg (R) B (MonoidAlgebra.single g r) = r • (R g).map (algebraMap A B) := by
    unfold W.GDet.repAlg
    rw [MonoidAlgebra.lift_single]
    rfl
  have rep_map {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A T) :
      W.GDet.repAlg (R) A[X] (MonoidAlgebra.mapRingHom T (algebraMap A A[X]) y) =
        (W.GDet.repAlg (R) A y).map (algebraMap A A[X]) := by
    induction y using MonoidAlgebra.induction_on with
    | of g => simp [MonoidAlgebra.of_apply, rep_single R]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
      ext i j
      simp
    | smul r x hx =>
      have hr : r • x = MonoidAlgebra.single 1 r * x := by
        rw [Algebra.smul_def]
        rfl
      have hm : MonoidAlgebra.mapRingHom T (algebraMap A A[X]) (MonoidAlgebra.single 1 r)
          = MonoidAlgebra.single 1 (algebraMap A A[X] r) := by
        ext g
        simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, rep_single R, rep_single R, map_one]
      congr 1
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have rep_chi {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A T) :
      (W.GDet.ofRep (R)).chi y = (W.GDet.repAlg (R) A y).charpoly := by
    unfold W.GDet.chi
    change (W.GDet.repAlg (R) A[X] _).det = _
    rw [← Polynomial.algebraMap_eq, map_sub, rep_single R, rep_map R, map_one]
    rw [Matrix.charpoly]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]
  have rep_trace {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A T) :
      (W.GDet.ofRep (R)).tr y = (W.GDet.repAlg (R) A y).trace := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    unfold W.GDet.tr W.GDet.lam
    rw [rep_chi R, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
    ring
  have rep_chi_single {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (g : T) :
      (W.GDet.ofRep (R)).chi (MonoidAlgebra.single g 1) = (R g).charpoly := by
    rw [rep_chi R, rep_single R]
    simp
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, chi_single]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (Ws.Eb.trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [rep_trace (W.mat ρ), rep_trace (W.mat ρ)] at e
      rw [rep_trace (W.mat ρ), mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, rep_chi_single (W.mat ρ), rep_chi_single (W.mat ρ₀), hm]
