module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

@[expose] public section

namespace Formalism.UG.P

theorem hecke_algebra_GL_commutative : Formalism.UG.HeckeCommGL := hecke_algebra_GL_comm_of_cartan cartan_decomposition_holds

theorem satake_transform_hecke_operator_Tj : Formalism.UG.SatakeTj := satake_Tj_of_spherical_cosets exists_spherical_function Tj_double_coset_decomposition

end Formalism.UG.P
