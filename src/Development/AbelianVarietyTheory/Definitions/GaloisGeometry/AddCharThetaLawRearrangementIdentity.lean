module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemStdLatticeIffIntegralCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
public import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.MainNotions.N IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NJoin.Inh

section Frame

variable {D : D7} {V : HSp D} {n : ℕ} (P : RowPsi V n)

variable (c : CoefA V)

variable (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank)

variable {W : Type} [AddCommGroup W] [Module ℂ W] (e : c.W ≃ₗ[ℂ] W)

variable (hc : ∀ h ∈ GfC V, c.ρ h = 1) (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ D.host.E n) W)
  (rat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h))
  (wt : ∀ (h : ReciprocityTheory.Aut.GQ D.host.E n), ∀ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h) →
    ∀ v, e (c.ρ γ v) = ρ h (e v))
include hc rat wt


end Frame

section Algebraic

open MvPolynomial ReciprocityTheory.Aut
open scoped Matrix

variable {ι : Type} [Fintype ι] {n : ℕ}

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

end Algebraic

section Weight

variable {D : D7}

theorem rat_unit {V : HSp D} (hg : V.gram = 1) (h : Formalism.AUTREP.GAf D.host.E V.rank) :
    h ∈ ReciprocityTheory.Aut.GQ D.host.E V.rank ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V ((GlobalTheory.StdFrameModel.unitPsi hg).ψ h) := by
  have hfin : finHom V ((GlobalTheory.StdFrameModel.unitPsi hg).ψ h) = Formalism.UG.bc (GlobalTheory.StdFrameModel.sw D).symm.toRingHom h.1 :=
    (GlobalTheory.StdFrameModel.exists_lift hg h).choose_spec.2
  have hU : ∀ x : GL (Fin V.rank) D.host.E, x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank ↔
      x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    intro x
    change x.1 * ReciprocityTheory.Aut.conjT _ x.1 = 1 ↔ Formalism.UG.cT _ x.1 * V.gram * x.1 = V.gram
    rw [hg, Matrix.mul_one, mul_eq_one_comm]
    rfl
  rw [hfin]
  constructor
  · rintro ⟨x, hx, e⟩
    have hx' := (hU x).1 hx
    have hm : Formalism.UG.bc (incA D) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
      have h0 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1 = V.gram := hx'
      have h2 := congrArg (fun M => Matrix.map M (incA D)) h0
      simp only [Matrix.map_mul] at h2
      exact h2
    refine ⟨⟨_, hm⟩, ⟨x, hx', rfl⟩, ?_⟩
    have e' : h.1 = _ := e.symm
    rw [e']
    ext i j
    change (sndA D.host.F 1) ⊗ₜ[D.host.F] (x.1 i j) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x.1 i j)
    rw [map_one]
  · rintro ⟨γ, ⟨x, hx, e⟩, e2⟩
    refine ⟨x, (hU x).2 hx, ?_⟩
    ext i j
    have e3 := congrArg (fun g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e2
    have e4 : (finHom V γ).1 i j = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x.1 i j) := by
      have e' : γ.1 = _ := e.symm
      change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (γ.1.1 i j) = _
      rw [e']
      change (sndA D.host.F 1) ⊗ₜ[D.host.F] (x.1 i j) = _
      rw [map_one]
    simp only [e4] at e3
    apply (GlobalTheory.StdFrameModel.sw D).symm.injective
    exact e3

variable {V : HSp D} (c : CoefA V)

end Weight

section Agreement

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : RealAt D cf nch tp)

end Agreement

section Reading

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {cf : CharFrame D} {nch : NChoice D}


end Reading

section Record

open Formalism.MainNotions Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.SPer (Dcf Zs)} {Zscf : Indef.DefSub P.A3.fam3.amb3 → Indef.IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : RealT Rc P Dcf Spf Zscf S Ks}

end Record

end GlobalTheory.NJoin.Inh

end
