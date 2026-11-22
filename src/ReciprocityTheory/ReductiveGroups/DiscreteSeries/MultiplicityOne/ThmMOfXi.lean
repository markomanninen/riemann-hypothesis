module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TheoremMOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeHerm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquiv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepro
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrame
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UuInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSymBeta
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRankOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem thmM_of_xi (h : UnitaryGroupStructuralFacts) (hXi : Formalism.FourierDecayAlt.B.XiExists) : ThmM :=
  theoremM_of h hXi (stBeHerm h) (stBePos h) (stSchurW h) (stSInt h) stSchurG (stPairs h) (stBeConv h) (stBeEquiv h)
    (stRepro h) (stSmooth h) stFrame (stInvGroup h) stInvChar stInvCC (stReps h) (stTransM h) (stSym h) (stSymBeta h)
    (stBetaInf h) (stDichoG h) (stDichoW h) (stMixed h) rankOneMinors

theorem thmM : ThmM := thmM_of_xi multiplicity_one_hypotheses_hold ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end ReciprocityTheory.ChartRestriction.DS.Mult1
