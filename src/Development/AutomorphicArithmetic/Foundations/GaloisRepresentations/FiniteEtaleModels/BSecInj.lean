module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecInj

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt Pulled UKer)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.secInjG_of :
    UpperTheory.Gal.crystallineComparison.Mod.PulledEx → UpperTheory.Gal.crystallineComparison.Mod.PulledRead → UpperTheory.Gal.crystallineComparison.Mod.PullKer → UpperTheory.Gal.crystallineComparison.Mod.KerFromU → UpperTheory.Gal.crystallineComparison.Mod.IsoOfKer → SecInjG := by
  intro hPE hPR hPK hKU hIK p _ D R _ b N hN hNp hm r w j e hw hu hj he M T K _ _ _ x y y' hy hy' hK
  have hpK0 : IsUnit ((p : ℕ) : K) := by
    refine IsUnit.mk0 _ ?_
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpK : IsUnit ((p : ℕ) : Γ(Sp K, ⊤)) := by
    have := hpK0.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp K) M.s x M.univ
  obtain ⟨P⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y hy
  obtain ⟨P'⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y' hy'
  have hc : ∃ e', p ^ e = p ^ e' ∧ (0 < j → 0 < e') := ⟨e, rfl, he⟩
  have kernel_imp (z z' : Sp K ⟶ T.Y) (hz : z ≫ T.s = x) (hz' : z' ≫ T.s = x)
      (hpoint : ∀ a : Over.mk x ⟶ M.univ.A,
        ES.KilledBy M.univ w a → KerAt T z a.left → KerAt T z' a.left)
      (Q : Pulled T m₁ z) (Q' : Pulled T m₁ z') (U : Over (Sp K)) (g : U ⟶ o₁.A)
      (hg : UKer r o₁ Q.ψ U g) : UKer r o₁ Q'.ψ U g := by
    obtain ⟨S, -, i, -, -, hfin, het, -, -, hiff⟩ :=
      ES.KerUPart.exists_kerUPart p D R b N hN hNp hm r w j (p ^ e)
        hw hu hj hc (Sp K) (x ≫ M.s) hpK o₁ Q.o' Q.ψ Q.isog Q.tj
    refine ⟨?_, hg.2⟩
    obtain ⟨v, rfl⟩ := (hiff U g).1 hg
    suffices hi : i ≫ Q'.ψ = 1 by
      rw [Category.assoc, hi]
      simp
    have : IsReduced S.left := by
      have : IsAffine S.left := isAffine_of_isAffineHom S.hom
      have hE : (Scheme.Hom.appTop S.hom).hom.Etale :=
        HasRingHomProperty.appTop @Etale S.hom het
      have hF : IsField Γ(Sp K, ⊤) :=
        MulEquiv.isField (Field.toIsField K)
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
      let : Field Γ(Sp K, ⊤) := hF.toField
      let := (Scheme.Hom.appTop S.hom).hom.toAlgebra
      have : Algebra.Etale Γ(Sp K, ⊤) Γ(S.left, ⊤) := hE.toAlgebra
      have : _root_.IsReduced Γ(S.left, ⊤) :=
        Algebra.FormallyUnramified.isReduced_of_field Γ(Sp K, ⊤) Γ(S.left, ⊤)
      exact isReduced_of_isAffine_isReduced S.left
    have : IsProper Q'.o'.A.hom := IsAbelianScheme.proper (self := Q'.o'.ab)
    have : Smooth Q'.o'.A.hom := IsAbelianScheme.smooth (self := Q'.o'.ab)
    have : LocallyOfFiniteType ((i ≫ Q'.ψ).left ≫ Q'.o'.A.hom) := by
      rw [Over.w]
      infer_instance
    apply Over.OverMorphism.ext
    refine ext_of_apply_eq Q'.o'.A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ ?_ ?_
    · intro pt _ hpt
      let aK : 𝟙_ (Over (Sp K)) ⟶ S :=
        Over.homMk (pointOfClosedPoint S.hom pt hpt) (pointOfClosedPoint_comp S.hom pt hpt)
      let a := aK ≫ i
      have ha : UKer r o₁ Q.ψ _ a := (hiff _ _).2 ⟨aK, rfl⟩
      have hR := (hPR p D R b N M r w j (p ^ e) T (Sp K) x (x ≫ M.s) o₁ m₁ z hz Q a).1
      have hR' := (hPR p D R b N M r w j (p ^ e) T (Sp K) x (x ≫ M.s) o₁ m₁ z' hz' Q' a).1
      have hkw : ES.KilledBy o₁ w a := (Q.tj K (𝟙 _)).1 a ha.1 ha.2
      have hbase : (a.left ≫ m₁.φ) ≫ M.univ.A.hom = x := by
        rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w a]
        exact Category.id_comp x
      let a₀ : Over.mk x ⟶ M.univ.A := Over.homMk (a.left ≫ m₁.φ) hbase
      have htransport := (hPK p D R b N M.X (Sp K) M.s (x ≫ M.s) x M.univ M.univ o₁ o₁ m₁ m₁
        (𝟙 _) (𝟙 _) (by simp)).1 (𝟙_ (Over (Sp K))) (Over.mk x) rfl a a₀ (by
          rw [eqToHom_refl, Category.id_comp]
          rfl)
      have hzero : a ≫ Q'.ψ = 1 := hR'.2 (hpoint a₀ ((htransport.2.2 w).1 hkw) (hR.1 ha.1))
      have hclosed : aK.left (IsLocalRing.closedPoint K) = pt := pointOfClosedPoint_apply S.hom pt hpt _
      have heq : aK ≫ (i ≫ Q'.ψ) = aK ≫ (1 : S ⟶ Q'.o'.A) := by
        rw [← Category.assoc, show aK ≫ i = a from rfl, hzero]
        simp
      rw [← hclosed]
      exact congrArg (fun f : 𝟙_ (Over (Sp K)) ⟶ Q'.o'.A => f.left (IsLocalRing.closedPoint K)) heq
    · rw [Over.w, Over.w]
  have k1 := kernel_imp y y' hy hy' (fun g hg => (hK g hg).1) P P'
  have k2 := kernel_imp y' y hy' hy (fun g hg => (hK g hg).2) P' P
  have hker : ∀ (U : Over (Sp K)) (g : U ⟶ o₁.A), g ≫ P.ψ = 1 ↔ g ≫ P'.ψ = 1 := by
    intro U g
    constructor
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog
        (fun U g => ⟨k1 U g, k2 U g⟩) U g
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P'.o' P.o' P'.ψ P.ψ P'.isog P.isog
        (fun U g => ⟨k2 U g, k1 U g⟩) U g
  obtain ⟨m, hm'⟩ := hIK p D R b N K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hker
  obtain ⟨m'', hm''⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m P'.m'
  have hU := T.univ (Sp K) x o₁ P.o' m₁ P.ψ hpK P.isog P.tj
  have fix : ∀ (f : Sp K ⟶ T.Y) (_ : f = y') (n : GlobalTheory.UPel.HT.ObjMap P.o' T.o' f),
      ∃ n' : GlobalTheory.UPel.HT.ObjMap P.o' T.o' y', n'.φ = n.φ := by
    rintro f rfl n
    exact ⟨n, rfl⟩
  obtain ⟨n', hn'⟩ := fix _ (Category.id_comp y') m''
  refine hU.unique ⟨hy, P.m₀, P.m', P.sq⟩ ⟨hy', P'.m₀, n', ?_⟩
  rw [hn', hm'', ← Category.assoc, hm', P'.sq]
