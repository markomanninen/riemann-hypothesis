module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquivB

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem stBeEquiv (h : UnitaryGroupStructuralFacts) : StBeEquiv := by
  intro k r Wp _ _ _ D X _ _ u u' hI h0 hh0 m hm
  exact ⟨BeEquiv.beOp_left D X (BeEquiv.beFacts_of h D) u u' hI hh0 hm,
    BeEquiv.beOp_right D X (BeEquiv.beFacts_of h D) u u' hI hh0 hm⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
