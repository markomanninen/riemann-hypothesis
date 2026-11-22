module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open GlobalTheory.PDivGroup in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charP : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  intro p _ k _ _ _ B f _
  obtain ⟨G, -, ⟨t⟩⟩ := GlobalTheory.AVTower.exists_tower p k B
  let T := GlobalTheory.Dieu.theory p
  have : Module.Free (WittVector p k) (T.M G) := T.base.free G trivial
  have : Module.Finite (WittVector p k) (T.M G) := T.base.finite G trivial
  have hWitt := GlobalTheory.Dieu.CharpolyAV.charpoly_map_eq p T k B G t (End.of f)
  have hπ : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) := fun x =>
    ⟨WittVector.teichmuller p x, by simp⟩
  obtain ⟨hfin, hRed⟩ := GlobalTheory.DeRhamCharpolyP.charpoly_of_red
    (WittVector.constantCoeff : WittVector p k →+* k) hπ p
    (CharP.cast_eq_zero k p) (T.red G) (T.base.red_surjective G trivial) (T.base.red_eq_zero G trivial)
    (T.map (t.map t f.hom)) (rigExtMap (t.map t f.hom)) (fun m => by
      have h := T.base.red_smap trivial trivial (SemiHom.ofHom (t.map t f.hom)) m
      rw [SemiHom.ofHom_rig] at h
      exact h)
  obtain ⟨e, he, -, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hR : IsNilpotent (p : k) := by
    rw [CharP.cast_eq_zero]
    exact IsNilpotent.zero
  let E := e hR B.ab t
  have : Module.Finite k G.RigExt := hfin
  have : Module.Finite k (primDR B.X) := Module.Finite.equiv E.symm
  have : Module.Free k G.RigExt := Module.Free.of_divisionRing k G.RigExt
  have hConj : primPull (dp0 k) (𝟙 _) f.hom = E.symm.conj (rigExtMap (t.map t f.hom)) := by
    refine LinearMap.ext fun c => ?_
    change primPull (dp0 k) (𝟙 _) f.hom c = E.symm (rigExtMap (t.map t f.hom) (E c))
    exact E.eq_symm_apply.mpr (he.primPull hR B.ab B.ab t t f.hom c)
  calc
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
        ((primPull (dp0 k) (𝟙 _) f.hom).dualMap).charpoly := rfl
    _ = (primPull (dp0 k) (𝟙 _) f.hom).charpoly := GlobalTheory.DeRhamCharpolyP.charpoly_dualMap _
    _ = (rigExtMap (t.map t f.hom)).charpoly :=
      (congrArg (fun φ : Module.End k (primDR B.X) => φ.charpoly) hConj).trans
        (E.symm.charpoly_conj _)
    _ = ((GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom (WittVector p k))).map
        WittVector.constantCoeff := hRed.trans (congrArg (Polynomial.map WittVector.constantCoeff) hWitt)
    _ = (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
