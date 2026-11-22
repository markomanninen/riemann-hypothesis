module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.tjExG_of :
    UpperTheory.Gal.crystallineComparison.Mod.EsNorm → UpperTheory.Gal.crystallineComparison.Mod.EsGen → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → UpperTheory.Gal.crystallineComparison.Mod.PullIsog → UpperTheory.Gal.crystallineComparison.Mod.PullKer → TjExG := by
  intro hN hG hT hPI hPK p _ D R _ _ _ _ b N h3 hcp hpm hm1 r w j e hw hle hj he M
  obtain ⟨Y, s, t, o, o', ms, mt, ψ, hst, hfs, -, -, -, hiso, htj, hu⟩ :=
    hN p D R b N h3 hcp hpm r w j (p ^ e) hw hle hj ⟨e, rfl, he⟩ hm1 M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, hgse, -, -, hiso0, htj0, hu0⟩ :=
    hG p D R b N h3 hcp hpm r w j (p ^ e) hw hle hj ⟨e, rfl, he⟩ hm1 M
  let U := M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))
  let V := s ⁻¹ᵁ U
  have het : Etale (s ∣_ U) := by
    have hpU : IsUnit ((p : ℕ) : Γ(U.toScheme, ⊤)) := by
      have h := GlobalTheory.EtC.PairDich.isUnit_ι_appTop U ((p : ℕ) : Γ(M.X, ⊤)) le_rfl
      rwa [map_natCast] at h
    have hp₀ : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := by
      simpa only [map_natCast] using hpU.map gs.appTop.hom
    have hpV : IsUnit ((p : ℕ) : Γ(V.toScheme, ⊤)) := by
      simpa only [map_natCast] using hpU.map (s ∣_ U).appTop.hom
    have hPB := isPullback_morphismRestrict s U
    obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N
      M.X V.toScheme M.s (V.ι ≫ s) M.univ
    obtain ⟨mVo, -⟩ := (hT p D R b N h3 hcp _ Y M.X _ (s ≫ M.s) M.s oV o M.univ V.ι s).2
      _ rfl mV ms
    obtain ⟨oV', mV', ψV, isoV, sqV⟩ := hPI p D R b N Y V.toScheme (s ≫ M.s) _ V.ι
      (Category.assoc _ _ _).symm (p ^ e) o o' ψ hiso oV mVo
    have tjV := (hPK p D R b N Y _ (s ≫ M.s) _ V.ι o o' oV oV' mVo mV' ψ ψV sqV).2 r w j htj
    obtain ⟨y₀, ⟨hy₀, m₀y, m₁y, hsq₀⟩, -⟩ := hu Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ hiso0 htj0
    obtain ⟨v, ⟨hv, m₀v, m₁v, hsqv⟩, -⟩ := hu0 _ (V.ι ≫ s) oV oV' mV ψV hpV isoV tjV
    have hvy : v ≫ y₀ = V.ι := by
      apply (hu _ (V.ι ≫ s) oV oV' mV ψV hpV isoV tjV).unique
      · refine ⟨by rw [Category.assoc, hy₀, hv], ?_⟩
        obtain ⟨a, ha⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀v m₀y
        obtain ⟨a', ha'⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁v m₁y
        refine ⟨a, a', ?_⟩
        rw [ha, ha', Category.assoc m₀v.φ m₀y.φ, hsq₀, ← Category.assoc m₀v.φ, hsqv,
          Category.assoc (Over.Hom.left ψV) m₁v.φ m₁y.φ]
      · exact ⟨rfl, mVo, mV', sqV⟩
    let u : Y₀ ⟶ V.toScheme := hPB.lift gs y₀ (by rw [hgs, hy₀])
    have hu₁ : u ≫ s ∣_ U = gs := hPB.lift_fst _ _ _
    have hu₂ : u ≫ V.ι = y₀ := hPB.lift_snd _ _ _
    have hvg : v ≫ gs = s ∣_ U := by
      rw [← cancel_mono U.ι, Category.assoc, hgs, hv, morphismRestrict_ι]
    have hvu : v ≫ u = 𝟙 _ := by
      apply hPB.hom_ext
      · rw [Category.assoc, hu₁, hvg, Category.id_comp]
      · rw [Category.assoc, hu₂, hvy, Category.id_comp]
    have huv : u ≫ v = 𝟙 Y₀ := by
      apply (hu0 Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ hiso0 htj0).unique
      · refine ⟨by rw [Category.assoc, hv, ← Category.assoc, hu₂, hy₀], ?_⟩
        have hc : (u ≫ v) ≫ y₀ = y₀ := by rw [Category.assoc, hvy, hu₂]
        obtain ⟨a, ha⟩ := (hT p D R b N h3 hcp Y₀ Y₀ Y _ _ _ o₀ o₀ o (u ≫ v) y₀).2 y₀ hc m₀y m₀y
        obtain ⟨a', ha'⟩ := (hT p D R b N h3 hcp Y₀ Y₀ Y _ _ _ o₀' o₀' o' (u ≫ v) y₀).2
          y₀ hc m₁y m₁y
        refine ⟨a, a', ?_⟩
        apply m₁y.cart.1.hom_ext
        · rw [Category.assoc a.φ, ← hsq₀, ← Category.assoc a.φ, ha, hsq₀,
            Category.assoc (Over.Hom.left ψ₀) a'.φ, ha']
        · have e1 := a.cart.1.w
          have e2 := a'.cart.1.w
          calc (a.φ ≫ Over.Hom.left ψ₀) ≫ o₀'.A.hom = a.φ ≫ o₀.A.hom := by rw [Category.assoc a.φ, Over.w]
            _ = o₀.A.hom ≫ (u ≫ v) := e1
            _ = (Over.Hom.left ψ₀ ≫ o₀'.A.hom) ≫ (u ≫ v) := by rw [Over.w]
            _ = (Over.Hom.left ψ₀ ≫ a'.φ) ≫ o₀'.A.hom := by
              rw [Category.assoc (Over.Hom.left ψ₀) o₀'.A.hom, ← e2,
                Category.assoc (Over.Hom.left ψ₀) a'.φ]
      · refine ⟨Category.id_comp _, ?_⟩
        have existsId {S S₃ : Scheme.{0}} {s : S ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
            {o : Obj b N s} {o₃ : Obj b N s₃} {g : S ⟶ S₃} (m : ObjMap o o₃ g) :
            ∃ i : ObjMap o o (𝟙 S), i.φ = 𝟙 _ := by
          obtain ⟨i, hi⟩ := (hT p D R b N h3 hcp _ _ _ _ _ _ o o o₃ (𝟙 S) g).2 g
            (Category.id_comp g) m m
          refine ⟨i, m.cart.1.hom_ext ?_ ?_⟩
          · rw [hi, Category.id_comp]
          · rw [i.cart.1.w, Category.comp_id, Category.id_comp]
        obtain ⟨i, hi⟩ := existsId ms₀
        obtain ⟨i', hi'⟩ := existsId m₁y
        exact ⟨i, i', by rw [hi, hi', Category.id_comp, Category.comp_id]⟩
    have : IsIso v := ⟨⟨u, hvu, huv⟩⟩
    rw [← hvg]
    infer_instance
  exact ⟨⟨Y, s, t, hst, o, o', ms, mt, ψ, hfs, het, hiso, htj, hu⟩⟩
