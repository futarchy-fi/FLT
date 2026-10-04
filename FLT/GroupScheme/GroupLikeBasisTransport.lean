/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GroupAlgebraCoactionBasis
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Transport of integral group-like bases

An integral Hopf comparison transports the standard basis, its multiplication,
comultiplication and counit. These are equalities for the original coordinate algebra.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace CoactionBasis

variable {R G H : Type*} [CommRing R] [CommGroup G] [CommRing H] [Bialgebra R H]
  (e : MonoidAlgebra R G ≃ₐc[R] H)

/-- The group-algebra basis transported through an integral bialgebra equivalence. -/
def transportedGroupBasis : Module.Basis G R H := (MonoidAlgebra.basis G R).map e.toLinearEquiv

/-- The identity degree is the unit of the original coordinate algebra. -/
theorem transportedGroupBasis_one : transportedGroupBasis e 1 = 1 := by
  change e (MonoidAlgebra.basis G R 1) = 1
  rw [groupAlgebraBasis_one, map_one]

/-- Degree multiplication is preserved integrally. -/
theorem transportedGroupBasis_mul (i j : G) :
    transportedGroupBasis e (i * j) = transportedGroupBasis e i * transportedGroupBasis e j := by
  change e (MonoidAlgebra.basis G R (i * j)) = _
  rw [groupAlgebraBasis_mul, map_mul]
  rfl

/-- Every transported basis vector is group-like in the original coalgebra. -/
theorem transportedGroupBasis_groupLike (i : G) :
    IsGroupLikeElem R (transportedGroupBasis e i) := by
  exact (MonoidAlgebra.isGroupLikeElem_single_one i).map e

/-- The basis diagonal is the original comultiplication. -/
theorem transportedGroupBasis_diagonal : diagonal (transportedGroupBasis e) = Coalgebra.comul := by
  apply (transportedGroupBasis e).ext
  intro i
  rw [diagonal_basis, (transportedGroupBasis_groupLike e i).comul_eq_tmul_self]

/-- The basis augmentation is the original counit. -/
theorem transportedGroupBasis_augmentation :
    augmentation (transportedGroupBasis e) = Coalgebra.counit := by
  apply (transportedGroupBasis e).ext
  intro i
  rw [augmentation_basis, (transportedGroupBasis_groupLike e i).counit_eq_one]

end CoactionBasis
