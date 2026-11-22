module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.AffineBCSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine

@[expose] public section

set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

theorem affineBCSt : AffineBCSt := by
  intro G B G' B' g q' q b sq hq X _ V hV V' hV' hle hleG φ φ' hφ' hφ
  exact coord_affineBC sq hq hV hV' hle hleG φ φ' hφ' hφ

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
