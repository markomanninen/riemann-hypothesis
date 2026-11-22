module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelRelationTwoX
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.CA Formalism.MainNotions.N
namespace UpperTheory.V.J
theorem irrOpenW_alt : _root_.UpperTheory.V.J.IrrOpenAlt := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B ι J hn hE x hx
  have irr_iff_span {Γ : Type} [Group Γ] (r : Γ →* GL (Fin n) (Qbar l)) :
      IsIrr r ↔ Submodule.span (Qbar l) (Set.range (mat r)) = ⊤ := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [← UpperTheory.V.AlgebraTools.Det.irrIffSpan]
    constructor
    · intro h N hN
      obtain ⟨-, -, hIrr⟩ := h
      exact hIrr N le_top fun g v hv => hN g v hv
    · intro h
      exact ⟨top_ne_bot, fun g v _ => Submodule.mem_top, fun N _ hN => h N fun g v hv => hN g v hv⟩
  have gram_at {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K]
      (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
      (h : (D.map f).comap φ = GDet.ofRep ρ) (g : Fin n × Fin n → H) :
      f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (φ (g a * g b)) 1))) =
        Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g b)).trace) := by
    have trace_at (a : H) : f (D.tr (MonoidAlgebra.single (φ a) 1)) = (ρ a).trace := by
      have hmap : f (D.tr (MonoidAlgebra.single (φ a) 1)) =
          (D.map f).tr (MonoidAlgebra.single (φ a) 1) := by
        have hcoeff := ((d_gmap D).2.2.1 f (MonoidAlgebra.single (φ a) 1)).2 1
        simpa [GDet.tr, MonoidAlgebra.coeff_mapRingHom] using hcoeff.symm
      have hcomap : ((D.map f).comap φ).tr (MonoidAlgebra.single a 1) =
          (D.map f).tr (MonoidAlgebra.single (φ a) 1) := by
        have hchi : ((D.map f).comap φ).chi (MonoidAlgebra.single a 1) =
            (D.map f).chi (MonoidAlgebra.single (φ a) 1) := by
          show (D.map f).D (Polynomial K) (MonoidAlgebra.mapDomainRingHom (Polynomial K) φ
            (MonoidAlgebra.single 1 Polynomial.X -
              MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single a 1))) = _
          congr 1
          rw [map_sub]
          simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
        simp only [GDet.tr, GDet.lam, hchi]
      rw [hmap, ← hcomap, h, ← (d_toDet _ _).2.2.1, d_toDet_ofRep.1 ρ,
        (d_ofRep _ _ _).2.2.1 hn, GDet.repAlg, MonoidAlgebra.lift_single, one_smul]
      congr 1
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [trace_at, map_mul]
  obtain ⟨ρ, -, hρ, hirr⟩ := hx
  obtain ⟨m, hm, hdet⟩ := (g_gram _ _ _).1 ((irr_iff_span ρ).1 hirr)
  choose g hg using hm
  refine ⟨Matrix.det (Matrix.of fun a b => B.u.D.tr (MonoidAlgebra.single (V.pr (g a * g b)) 1)), ?_, ?_⟩
  · intro h0
    refine hdet ?_
    have h1 := gram_at B.u.D (x : B.B →+* Qbar l) V.pr (mat ρ) hρ g
    have h2 := h1.symm.trans h0
    simpa only [hg] using h2
  · intro y w hJ hy hy0
    have hA : y.Arith w := ⟨hy.1, fun v j => by
      obtain ⟨ph, hph, -⟩ := hy.2 v
      exact ⟨ph j, hph j⟩⟩
    obtain ⟨ρ', hc', -, hρ', -⟩ := _root_.UpperTheory.GalN.V.end1W' hE y w hJ hA
    refine ⟨ρ', hc', hρ', (irr_iff_span ρ').2 ((g_gram _ _ _).2 ⟨fun a => mat ρ' (g a), fun a => ⟨_, rfl⟩, fun h => hy0 ?_⟩)⟩
    have h1 := gram_at B.u.D (y : B.B →+* Qbar l) V.pr (mat ρ') hρ' g
    exact h1.trans h
end UpperTheory.V.J
end
end
