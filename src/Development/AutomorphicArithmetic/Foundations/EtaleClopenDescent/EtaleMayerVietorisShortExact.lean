module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExactStatement

@[expose] public section

theorem UpperTheory.Cb.etale_mayer_vietoris_short_exact :
    LateralTheory.E.MayerVietorisSequence.SES := by
  intro R _ U V E f g h
  exact GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
