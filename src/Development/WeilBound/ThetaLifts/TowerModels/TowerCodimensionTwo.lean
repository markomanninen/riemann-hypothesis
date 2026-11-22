module

public import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwoOf
public import Development.WeilBound.ThetaLifts.TowerModels.LeviEx
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneSkew
public import Development.WeilBound.ThetaLifts.TowerModels.StabEx
public import Development.WeilBound.ThetaLifts.TowerModels.ModelEx
public import Development.WeilBound.ThetaLifts.TowerModels.DetHerm
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeEx : PlaneEx := ⟨planeHerm, planeSkew⟩

end PositivityTheory.ThKG.Tow

end
