module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTop
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLat
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpUniq
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpCount
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLift
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTwBasic
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpRes
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiEta
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpOrd
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiSub
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpSupp
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector

@[expose] public section

namespace UpperTheory.TNZ.Grp

theorem step_suppProd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.SupportOfProductProp :=
  step_spTop G UpperTheory.TNZ.step_spLat (step_spUniq G) (step_spCount G) (step_spLift G) (step_spTwBasic G) (step_spRes G)
    (step_spPiEta G) step_spOrd (step_spPiSub G) (step_spSupp G) UpperTheory.TNZ.step_cuspSupp UpperTheory.TNZ.step_prodIrr
    UpperTheory.TNZ.step_tensorVec

end UpperTheory.TNZ.Grp
