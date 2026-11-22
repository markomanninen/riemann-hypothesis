module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFixedMkEqOfCommute
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedInjSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenGx
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactParahoricSubgroupStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricLeviUnipotentLowerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLowerStatement

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasadTop

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem moyPrasadJacquetIso : GlobalTheory.Published.MoyPrasadJacquetIso := by
  intro k _ _ _ _ n s d e V _ _ π hπ
  refine ⟨mapsTo_fixed_jacU e π _, ?_, ?_⟩
  · intro v hv w hw h
    have h0 : (Submodule.Quotient.mk (v - w) : Jacquet π (unipRad k e)) = 0 := by
      rw [Submodule.Quotient.mk_sub]
      exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.DepthZeroJac.fixed_inj_smooth k n s d e V π hπ.1 (v - w) (sub_mem hv hw) h0)
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := GlobalTheory.CompanionTheory.JacquetCentral.exists_fixed_mk_eq_of_commute π hπ (Gx k e) (unipRad k e) (GlobalTheory.CompanionTheory.MoyPrasad.isOpen_Gx k n s d e)
      (GlobalTheory.T.isCompact_parahoric_subgroup k n s d e) (leviEmb k e) (leviEmb_mem_normalizer k e) ((Gx k e).comap (leviEmb k e))
      (fun _ hm => hm) (lowC k e) (GlobalTheory.T.parahoric_levi_unipotent_lower k n s d e)
      (fun U hU => by
        refine (GlobalTheory.T.central_torus_contracts_lower k n s d e U hU).imp ?_
        intro t ht
        exact ⟨fun m _ => ht.1 m, ht.2⟩) y hy
    exact ⟨v, hv, hvy⟩

end GlobalTheory.CompanionTheory.MoyPrasadTop

end
