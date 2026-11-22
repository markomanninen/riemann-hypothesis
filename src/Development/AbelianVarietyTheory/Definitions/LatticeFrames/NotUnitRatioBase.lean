module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.Top.Model
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Check

variable {D : D7}

section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

variable {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S} (eW : Pm.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ))
  (j : SmT MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X')

theorem ReadsG.period_eq {G G' : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)} (h : ReadsG K eW j x G f) (h' : ReadsG K eW j x G' f)
    (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) : Pm.period w G = Pm.period w G' := by
  choose v hv using hw
  have e : w = ∑ c, eW.symm (Pi.single c (j (v c))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, LinearEquiv.eq_symm_apply]
    simp only [hv]
    exact (Finset.univ_sum_single _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := hasMat_exists (K.y c)
  have hc : (Nat.card (M.stabilizer₂ c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := M.stabilizer₂ c)).ne'
  exact mul_left_cancel₀ hc ((h c _ g hg).symm.trans (h' c _ g hg))

end Read

section Package

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {P : LevelP R.Pg D.R.r ℂ} {u : D.what₂.Word} {g : Geo D}

theorem colCh_nonempty (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : ∃ k : ColCh u C, ∀ j, Nonempty (k.Ch j) :=
  by
    let k : ColCh u C :=
      { kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => Finsupp.single 1 1, eT := fun _ _ _ => Finsupp.single 1 1,
        Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }
    exact ⟨k, fun _ => ⟨()⟩⟩

end Package

section Real

open GlobalTheory.MiS

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

end Real

end GlobalTheory.Fam.Check

end
