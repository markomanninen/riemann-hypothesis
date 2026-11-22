module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RedOne

theorem redFn_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (PP : Pl D.host.E), Lev.finE V g ∈ Formalism.L2.DIV.St β → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V g) = 1 := by
  intro D V β g PP hS h1
  classical
  exact GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS
    (fun v hv => by rw [Finset.mem_singleton] at hv; subst hv; exact h1) (Finset.mem_singleton_self _)

end GlobalTheory.ChainOnto.RedOne
