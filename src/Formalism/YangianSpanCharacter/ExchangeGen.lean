module

public import Formalism.YangianSpanCharacter.StatementT

@[expose] public section

namespace Formalism.YangianSpanCharacter.T

open Matrix

def E1 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then M ik.1 jl.1 else 0

def E2 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then M ik.2 jl.2 else 0

end Formalism.YangianSpanCharacter.T
