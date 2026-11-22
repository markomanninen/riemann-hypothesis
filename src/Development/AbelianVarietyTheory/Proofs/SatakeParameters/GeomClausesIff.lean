module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AssocSetApplyOfPointwise
public import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

section
variable (f : X ⟶ Y)

end

variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

def ObjMap.ptEquiv (m : ObjMap o' o f) (T : Over S') : (T ⟶ o'.A) ≃* ((Over.map f).obj T ⟶ o.A) :=
  MulEquiv.ofBijective (pushHom m.cart T) ⟨GlobalTheory.SiegelPull.push_injective m.cart T, GlobalTheory.SiegelPull.push_surjective m.cart T⟩

theorem ObjMap.ptEquiv_left (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) :
    (m.ptEquiv T x).left = x.left ≫ m.φ := rfl

theorem ObjMap.ptEquiv_act (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) (c : D.O) :
    m.ptEquiv T (x ≫ o'.act.act c) = m.ptEquiv T x ≫ o.act.act c :=
  Over.OverMorphism.ext (by
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, m.act,
      Category.assoc])

theorem ObjMap.exists_ptEquiv (m : ObjMap o' o f) (Z : Over S) (g : Z.left ⟶ S') (hg : g ≫ f = Z.hom) :
    ∃ σ : (Over.mk g ⟶ o'.A) ≃* (Z ⟶ o.A), (∀ x, (σ x).left = x.left ≫ m.φ) ∧
      ∀ (n : ℤ) (a c : Over.mk g ⟶ o'.A) (z : Γ(Z.left, ⊤)ˣ),
        (Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n a c z ↔
          Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (σ a) (σ c) z) := by
  obtain ⟨Zl, Zr, Zh⟩ := Z
  change Zl ⟶ S' at g
  change g ≫ f = Zh at hg
  subst hg
  refine ⟨m.ptEquiv (Over.mk g), fun x => rfl, fun n a c z => ?_⟩
  exact GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o'.isLB _)
    m.cart (GlobalTheory.SiegelPull.diag_iso m.sq m.pol) (Over.mk g) n a c _ _ z rfl rfl

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

end GlobalTheory.UPel.HT
