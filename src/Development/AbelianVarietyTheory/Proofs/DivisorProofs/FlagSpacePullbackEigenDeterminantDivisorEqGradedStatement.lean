module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpacePullbackEigenDeterminantDivisorEqGraded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

open GlobalTheory.EigDivPic GlobalTheory.ShFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpacePullback_eigenDeterminantDivisor_eq_gradedLines : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)) (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)), (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φ₀ → (∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)) (fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK → D.IsEqn x (∏ τ, (fK.isUnit_det_co f₀ τ).unit ^ (-a τ))) → CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) := by
  intro E _ _ _ H Dw l Xo c TF Z _ φ₀ f₀ a D h₀ hD
  have hL := pull_isLB (isLB_toLB D) (π₀ TF.X Z)
  have hM : (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1).IsLB := LB.isLB_pull (TF.X.F.isLB_LL _) _
  rw [← cls_pull (isLB_toLB D) _ hL, cls_eq_iff]
  refine exists_gen_of_rel (LB.isLB_div hM hL) (fun p => IsQuot TF Z f₀ a (p.1 PUnit.unit) (p.2 PUnit.unit).1.2)
    (fun p y hy => exists_isQuot TF Z f₀ a D h₀ hD _ _ _ (p.2 PUnit.unit).2.2 _ (fun _ h => mem_pull.1 (inf_le_left (a := (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1).U p.1)
        (b := ((toLB D).pull (π₀ TF.X Z)).U p.2) h))
      (fun _ h => mem_pull.1 (inf_le_right (a := (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1).U p.1)
        (b := ((toLB D).pull (π₀ TF.X Z)).U p.2) h)) y hy) fun p q y u u' hp hq h h' => ?_
  have h1 : inc₀ TF.X Z y ∈ TF.X.F.U (p.1 PUnit.unit) ⊓ TF.X.F.U (q.1 PUnit.unit) := ⟨mem_pull.1 hp.1, mem_pull.1 hq.1⟩
  have h2 : π₀ TF.X Z y ∈ (toLB D).U (p.2 PUnit.unit) ⊓ (toLB D).U (q.2 PUnit.unit) := ⟨mem_pull.1 hp.2, mem_pull.1 hq.2⟩
  rw [gm_div' _ _ (𝟙 _) y p q hp hq, gm_pull_g _ _ (𝟙 _) y _ _ hp.1 hq.1, gm_pull_g _ _ (𝟙 _) y _ _ hp.2 hq.2,
    Category.id_comp, Category.id_comp]
  refine (IsQuot.compare TF Z f₀ a h h' (top_le_stalk_preimage y _ h1) _ (gm_val_ev _ y _ h1 _ _)
    (Units.map ((X₀ TF.Y Z).presheaf.germ _ _ h2).hom.toMonoidHom ((toLB D).g _ _)) (Units.ext ?_)).trans ?_
  · rw [Units.val_div_eq_div_val, ← fnOf_toLB_g _ _ (gen_mem h2)]
    exact algebraMap_germ h2 _
  · congr 3
    exact Units.ext (gm_val_stalk _ y _ h2 _).symm

