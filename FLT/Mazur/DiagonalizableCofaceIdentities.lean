/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableCoefficientReduction

/-!
# Associativity identities for the actual character cofaces

These equalities are equalities of algebra maps on full character algebras.
They retain nilpotents and give the six cancellations in the full
multiplication-defect cocycle of an arbitrary scheme map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

variable (R G : Type*) [CommRing R] [AddCommMonoid G]

/-- The front/first and rightProduct/first substitutions agree on the full algebra. -/
theorem front_first_comp :
    (frontMap R G).comp (firstMap R G) =
      (rightProductMap R G).comp (firstMap R G) := by
  rw [frontMap, firstMap, rightProductMap,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

/-- The front/second and back/first substitutions agree on the full algebra. -/
theorem front_second_comp :
    (frontMap R G).comp (secondMap R G) =
      (backMap R G).comp (firstMap R G) := by
  rw [frontMap, secondMap, backMap, firstMap,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

/-- The front/diagonal and leftProduct/first substitutions agree on the full algebra. -/
theorem front_diagonal_comp :
    (frontMap R G).comp (diagonalMap R G) =
      (leftProductMap R G).comp (firstMap R G) := by
  rw [frontMap, diagonalMap, leftProductMap, firstMap,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

/-- The leftProduct/second and back/second substitutions agree on the full algebra. -/
theorem leftProduct_second_comp :
    (leftProductMap R G).comp (secondMap R G) =
      (backMap R G).comp (secondMap R G) := by
  rw [leftProductMap, secondMap, backMap,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

/-- The leftProduct/diagonal and rightProduct/diagonal substitutions agree on the full algebra. -/
theorem leftProduct_diagonal_comp :
    (leftProductMap R G).comp (diagonalMap R G) =
      (rightProductMap R G).comp (diagonalMap R G) := by
  rw [leftProductMap, diagonalMap, rightProductMap,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

/-- The back/diagonal and rightProduct/second substitutions agree on the full algebra. -/
theorem back_diagonal_comp :
    (backMap R G).comp (diagonalMap R G) =
      (rightProductMap R G).comp (secondMap R G) := by
  rw [backMap, diagonalMap, rightProductMap, secondMap,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

/-- The full base reduction commutes with the actual character algebra maps. -/
theorem coefficientReduction_mapDomain_comp {H : Type*} [AddCommMonoid H]
    (I : Ideal R) (f : G →+ H) :
    (coefficientReduction R H I).comp (AddMonoidAlgebra.mapDomainAlgHom R R f) =
      (AddMonoidAlgebra.mapDomainAlgHom R (R ⧸ I) f).comp (coefficientReduction R G I) :=
  AlgHom.ext (coefficientReduction_mapDomain R G I f)

end FLT.Mazur.DiagonalizableCobar
