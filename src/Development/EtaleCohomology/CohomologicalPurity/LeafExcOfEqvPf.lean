module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcLevelPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafChPushPf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

@[reassoc] theorem dinl_map {A B : Arrow Spc} (ψ : A ⟶ B) : dbl.inl A ≫ dbl.map ψ = ψ.right ≫ dbl.inl B :=
  pushout.inl_desc (f := A.hom) (g := A.hom) _ _ _

variable {P' P : Arrow Spc} (φ : P' ⟶ P)

def ii : P'.right ⟶ MM φ := pushout.inl P'.hom (P'.hom ≫ φ.right)
def jj : P.right ⟶ MM φ := pushout.inr P'.hom (P'.hom ≫ φ.right)
theorem ij_cond : P'.hom ≫ ii φ = (P'.hom ≫ φ.right) ≫ jj φ :=
  pushout.condition (f := P'.hom) (g := P'.hom ≫ φ.right)

def rr : MM φ ⟶ P.right :=
  pushout.desc (f := P'.hom) (g := P'.hom ≫ φ.right) φ.right (𝟙 _) (by simp)

def QQ : Arrow Spc := Arrow.mk (jj φ)

def chi : P' ⟶ QQ φ := Arrow.homMk (P'.hom ≫ φ.right) (ii φ) (ij_cond φ).symm

def sig : dbl (QQ φ) ⟶ MM φ :=
  pushout.desc (f := jj φ) (g := jj φ) (𝟙 _) (rr φ ≫ jj φ) (by
    have h : jj φ ≫ rr φ = 𝟙 _ :=
      pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    rw [← Category.assoc, h, Category.id_comp, Category.comp_id])

theorem inr_sig_gM : dbl.inr (QQ φ) ≫ sig φ ≫ gM φ = rr φ ≫ dbl.inr P := by
  have hs : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ :=
    pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _
  have hg : jj φ ≫ gM φ = dbl.inr P :=
    pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  rw [← Category.assoc, hs]
  change (rr φ ≫ jj φ) ≫ gM φ = rr φ ≫ dbl.inr P
  rw [Category.assoc, hg]

theorem hgM : dbl.map (chi φ) ≫ sig φ ≫ gM φ = dbl.map φ := by
  have hs : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ :=
    pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _
  have hg : ii φ ≫ gM φ = φ.right ≫ dbl.inl P :=
    pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  have hr : ii φ ≫ rr φ = φ.right :=
    pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  apply pushout.hom_ext
  · show dbl.inl P' ≫ _ = dbl.inl P' ≫ _
    rw [dinl_map_assoc, dinl_map, ← Category.assoc (dbl.inl (QQ φ)), hs]
    change ii φ ≫ 𝟙 (MM φ) ≫ gM φ = _
    rw [Category.id_comp]
    exact hg
  · show dbl.inr P' ≫ _ = dbl.inr P' ≫ _
    rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, inr_sig_gM]
    change ii φ ≫ rr φ ≫ dbl.inr P = _
    rw [← Category.assoc, hr]

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut
variable {P' P : Arrow Spc} (φ : P' ⟶ P)
theorem jj_inl : jj φ ≫ dbl.inl (QQ φ) = jj φ ≫ dbl.inr (QQ φ) :=
  pushout.condition (f := jj φ) (g := jj φ)

def LeafFix : Prop := ∀ (q : ℕ) (n i : ℤ) {P' P : Arrow Spc} (φ : P' ⟶ P) (z : Ht q (dbl (QQ φ)) n i),
  z ∈ Hs q (QQ φ) n i → pull _ (sig φ ≫ dbl.inl (QQ φ)) (tw q i) n z = z

def LeafChiExc : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), Exc q (chi φ)

theorem pull_sig_inl (q : ℕ) (n i : ℤ) (z : Ht q (dbl (QQ φ)) n i) :
    pull _ (sig φ) (tw q i) n (pull _ (dbl.inl (QQ φ)) (tw q i) n z) = pull _ (sig φ ≫ dbl.inl (QQ φ)) (tw q i) n z :=
  (pull_comp _ (sig φ) (dbl.inl (QQ φ)) _ n z).symm

theorem pull_jj_inl (q : ℕ) (n i : ℤ) (z : Ht q (dbl (QQ φ)) n i) (hz : z ∈ Hs q (QQ φ) n i) :
    pull _ (jj φ) (tw q i) n (pull _ (dbl.inl (QQ φ)) (tw q i) n z) = 0 := by
  have hzz : pull _ (dbl.inr (QQ φ)) (tw q i) n z = 0 := hz
  exact (pull_comp _ (jj φ) (dbl.inl (QQ φ)) _ n z).symm.trans
    ((congrArg (fun f => pull _ f (tw q i) n z) (jj_inl φ)).trans
      ((pull_comp _ (jj φ) (dbl.inr (QQ φ)) _ n z).trans ((congrArg (pull _ (jj φ) (tw q i) n) hzz).trans (map_zero _))))

theorem LeafExcOfEqv_of (hF : LeafFix) (hX : LeafChiExc) : LeafExcOfEqv := by
  intro q P' P φ hE n i
  have jj_gM : jj φ ≫ gM φ = dbl.inr P :=
    pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  have inr_sig : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ :=
    pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _
  have inl_sig : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ :=
    pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _
  have hB : Function.Bijective (pull _ (gM φ) (tw q i) n) := hE i n
  have hC := hX q φ n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    have hw' : pull _ (dbl.map φ) (tw q i) n w.1 = 0 := congrArg Subtype.val hw
    have hj : pull _ (jj φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) = 0 := by
      rw [← pull_comp, jj_gM]; exact w.2
    have hz : pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) ∈ Hs q (QQ φ) n i := by
      change pull _ (dbl.inr (QQ φ)) _ n (pull _ (sig φ) _ n _) = 0
      exact (pull_comp _ (dbl.inr (QQ φ)) (sig φ) _ n _).symm.trans
        ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) inr_sig).trans
          ((pull_comp _ (rr φ) (jj φ) _ n _).trans ((congrArg (pull _ (rr φ) (tw q i) n) hj).trans (map_zero _))))
    have h0 : Hs.pull q (chi φ) n i ⟨_, hz⟩ = Hs.pull q (chi φ) n i 0 := by
      rw [map_zero]
      apply Subtype.ext
      change pull _ (dbl.map (chi φ)) _ n (pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1)) = 0
      rw [← pull_comp, ← pull_comp, Category.assoc, hgM]; exact hw'
    have h1 := congrArg Subtype.val (hC.1 h0)
    change pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1) = 0 at h1
    have h2 : pull _ (gM φ) (tw q i) n w.1 = 0 := by
      have e := congrArg (pull _ (dbl.inl (QQ φ)) (tw q i) n) h1
      have e2 : pull _ (dbl.inl (QQ φ)) (tw q i) n (pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) =
          pull _ (gM φ) (tw q i) n w.1 :=
        (pull_comp _ (dbl.inl (QQ φ)) (sig φ) _ n _).symm.trans
          ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) inl_sig).trans (pull_id _ _ _ n _))
      rw [e2, map_zero] at e
      exact e
    apply Subtype.ext
    exact hB.1 (h2.trans (map_zero _).symm)
  · intro z'
    obtain ⟨z, hz⟩ := hC.2 z'
    obtain ⟨y', hy'⟩ := hB.2 (pull _ (dbl.inl (QQ φ)) (tw q i) n z.1)
    have hm : y' ∈ Hs q P n i := by
      change pull _ (dbl.inr P) _ n y' = 0
      rw [← jj_gM, pull_comp, hy']
      exact pull_jj_inl φ q n i z.1 z.2
    refine ⟨⟨y', hm⟩, ?_⟩
    rw [← hz]
    apply Subtype.ext
    change pull _ (dbl.map φ) _ n y' = pull _ (dbl.map (chi φ)) _ n z.1
    rw [← hgM, pull_comp, pull_comp, hy', pull_sig_inl, hF q n i φ z.1 z.2]

end LateralTheory.CohomologicalPurity.TubeCut
