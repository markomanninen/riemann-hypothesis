module

public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLine
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLineTall
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQPos
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQBilin
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivClosedGraded
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWInClosed
public import Formalism.GradedWeylDivisibility.StatementB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylEqNablaQ
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRationalOf

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem hwLine : HWLine := highest_weight_line
theorem hwLineTall : HWLineTall := highest_weight_line_tall
theorem fockQPos : FockQPos := fischerInnerRatPos
theorem fockQBilin : FockQBilin := fischerInnerRatBilinear
theorem fockQRowDivAdj : FockQRowDivAdj := fock_space_row_divided_adjoint
theorem rowDivClosedGraded : RowDivClosedGraded := row_divided_closed_graded
theorem hwInClosed : HWInClosed := hwInClosed_of hwLine rowDivClosedGraded
theorem closedEqNabla : ClosedEqNabla := closedEqNabla_of hwInClosed fockQPos fockQBilin fockQRowDivAdj
theorem weylEqNablaQ : WeylEqNablaQ := weylEqNablaQ_of closedEqNabla

theorem weylRational : WeylRational := weyl_module_rational weylEqNablaQ

end Formalism.GradedWeylDivisibility
