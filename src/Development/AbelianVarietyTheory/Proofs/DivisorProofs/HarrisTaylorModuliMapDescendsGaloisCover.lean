module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.MapDesc

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def objMapCongr {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {f g : S' ⟶ S} (m : ObjMap o' o f) (h : f = g) : ObjMap o' o g := h ▸ m

end GlobalTheory.UPel.HT.MapDesc


open GlobalTheory.UPel.HT.MapDesc GlobalTheory.UPel.HT.MapComp in
theorem GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
  (S S₁ Y : Scheme.{0}) (t : S ⟶ Sp R) (sY : Y ⟶ Sp R) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga]
  (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (o : Obj b N t) (o' : Obj b N (π₁ ≫ t)) (u : Obj b N sY),
  3 ≤ N → N.Coprime p → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → ObjMap o' o π₁ → ObjMap o' u (π₁ ≫ f) →
  Nonempty (ObjMap o u f) := by
  intro p _ D R _ b N S S₁ Y t sY π₁ Ga _ ρ₁ f o o' u hN hNp hG m₁ m₂
  let compose : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
      {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃},
      ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → ObjMap o₁ o₃ (f ≫ g) := fun {_ _ _} {_ _ _} {o₁ o₂ o₃} {_ _} m₁ m₂ =>
    { φ := m₁.φ ≫ m₂.φ
      φ₂ := m₁.φ₂ ≫ m₂.φ₂
      cart := m₁.cart.comp m₂.cart
      sq := MapComp.isSquare_comp m₁.sq m₂.sq
      act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
      pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol (MapComp.lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
      eta := fun y => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  have uniq : ∀ {T T' : Scheme.{0}} {sT : T ⟶ Sp R} {sT' : T' ⟶ Sp R} {x : Obj b N sT} {y : Obj b N sT'}
      {g g' : T ⟶ T'} (_ : g = g') (n : ObjMap x y g) (n' : ObjMap x y g'), n.φ = n'.φ := by
    rintro T T' sT sT' x y g g' rfl n n'
    exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique p D R b N hN hNp T' T sT' sT x y g n n'
  have hw : ∀ a, m₁.φ ≫ o.A.hom = (o'.A.hom ≫ ρ₁ a) ≫ π₁ := fun a => by
    rw [Category.assoc, hG.inv a]; exact m₁.cart.1.w
  let σ : Ga → (o'.A.left ⟶ o'.A.left) := fun a => m₁.cart.1.lift m₁.φ (o'.A.hom ≫ ρ₁ a) (hw a)
  have hσ₁ : ∀ a, σ a ≫ m₁.φ = m₁.φ := fun a => m₁.cart.1.lift_fst _ _ _
  have hσ₂ : ∀ a, σ a ≫ o'.A.hom = o'.A.hom ≫ ρ₁ a := fun a => m₁.cart.1.lift_snd _ _ _
  have hG' : GlobalTheory.ZM.IsGaloisCover Ga σ m₁.φ := hG.of_isPullback m₁.cart.1.flip hσ₂ hσ₁
  have hinv : ∀ a, σ a ≫ m₂.φ = m₂.φ := fun a => by
    obtain ⟨n⟩ := MapComp.cancel (f := ρ₁ a) (g := π₁) (objMapCongr m₁ (hG.inv a).symm) m₁
    have hn₁ : n.φ ≫ m₁.φ = m₁.φ := uniq (hG.inv a) (compose n m₁) m₁
    have hn₂ : n.φ ≫ o'.A.hom = o'.A.hom ≫ ρ₁ a := n.cart.1.w
    have hnσ : n.φ = σ a := m₁.cart.1.hom_ext (by rw [hn₁, hσ₁]) (by rw [hn₂, hσ₂])
    rw [← hnσ]
    exact uniq (show ρ₁ a ≫ (π₁ ≫ f) = π₁ ≫ f by rw [← Category.assoc, hG.inv a]) (compose n m₂) m₂
  obtain ⟨φ, hφ, -⟩ := hG'.existsUnique_desc m₂.φ hinv
  have : Epi m₁.φ := by
    have := hG'.etale; have := hG'.onto
    exact Flat.epi_of_flat_of_surjective _
  have : Epi π₁ := by
    have := hG.etale; have := hG.onto
    exact Flat.epi_of_flat_of_surjective _
  have cart : IsGrpPullback o.A u.A f φ :=
    GlobalTheory.T.isGrpPullback_descent_along_galoisCover S S₁ Y π₁ Ga ρ₁ f o'.A o.A u.A m₁.φ m₂.φ φ hG m₁.cart m₂.cart hφ
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare cart.1.w
  have sq₂ : IsSquare m₂.φ (m₁.φ₂ ≫ φ₂) := by rw [← hφ]; exact MapComp.isSquare_comp m₁.sq sq
  have e₂ : m₂.φ₂ = m₁.φ₂ ≫ φ₂ := MapComp.isSquare_unique m₂.sq sq₂
  have hA₂ : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab
  have := hA₂.comm
  obtain ⟨r, hr⟩ : GlobalTheory.AbLaw.Triv (o.P.pull (eSec (G2 o.A))) :=
    GlobalTheory.AbLaw.CubeOpen.triv_comp (eSec o.A) (GlobalTheory.SquareDescent.eSec_lift_one o.A) o.rig₁
  obtain ⟨r', hr'⟩ : GlobalTheory.AbLaw.Triv (u.P.pull (eSec (G2 u.A))) :=
    GlobalTheory.AbLaw.CubeOpen.triv_comp (eSec u.A) (GlobalTheory.SquareDescent.eSec_lift_one u.A) u.rig₁
  let PA : RigLB (G2 o.A) := ⟨o.P, r, o.isLB, hr⟩
  let PB : RigLB (G2 u.A) := ⟨u.P, r', u.isLB, hr'⟩
  have c₁ : IsGrpPullback (G2 o'.A) (G2 o.A) π₁ m₁.φ₂ :=
    GlobalTheory.ShearLift.isGrpPullback_tensor m₁.cart m₁.cart m₁.sq.1 m₁.sq.2
  have c₂ : IsGrpPullback (G2 o.A) (G2 u.A) f φ₂ := GlobalTheory.ShearLift.isGrpPullback_tensor cart cart sq.1 sq.2
  have pol₂ : LBIso o'.P (u.P.pull (m₁.φ₂ ≫ φ₂)) := by rw [← e₂]; exact m₂.pol
  have pol : LBIso o.P (u.P.pull φ₂) :=
    GlobalTheory.T.rigidLineBundleIso_descent_along_galoisCover S S₁ Y π₁ Ga ρ₁ f (G2 o'.A) (G2 o.A) (G2 u.A) m₁.φ₂ φ₂ PA PB o'.P hA₂ hG c₁ c₂ o'.isLB m₁.pol pol₂
  refine ⟨{ φ := φ, φ₂ := φ₂, cart := cart, sq := sq, act := fun c => ?_, pol := pol, eta := fun y => ?_ }⟩
  · rw [← cancel_epi m₁.φ, ← Category.assoc, ← m₁.act c, Category.assoc, hφ, m₂.act c, ← hφ, Category.assoc]
  · rw [← cancel_epi π₁, ← Category.assoc, ← m₁.eta y, Category.assoc, hφ, m₂.eta y, Category.assoc]
