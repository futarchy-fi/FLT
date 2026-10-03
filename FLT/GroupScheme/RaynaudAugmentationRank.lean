/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterCoordinates

/-!
# Rank of the actual augmentation ideal

The counit and unit split the coordinate module into constants and its
augmentation ideal. Generic evaluation then determines the total rank.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- The counit splits off the constants from the actual coordinate algebra. -/
def FF.augmentationSplit (X : FF R K) : X.CoordinateRing ≃ₗ[R] R × X.augmentation where
  toFun a := ⟨Coalgebra.counit a, ⟨a - algebraMap R X.CoordinateRing (Coalgebra.counit a), by
    change Coalgebra.counit (a - algebraMap R X.CoordinateRing (Coalgebra.counit a)) = 0
    simp⟩⟩
  invFun a := algebraMap R X.CoordinateRing a.1 + a.2
  left_inv a := by simp
  right_inv a := by
    have ha : Coalgebra.counit (R := R) (a.2 : X.CoordinateRing) = 0 := a.2.property
    apply Prod.ext
    · simp [ha]
    · apply Subtype.ext
      simp [ha]
  map_add' a b := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Subtype.ext
      simp only [map_add, Prod.snd_add, Submodule.coe_add]
      abel
  map_smul' r a := by
    apply Prod.ext
    · exact map_smul _ _ _
    · apply Subtype.ext
      simp [Algebra.smul_def, mul_sub]

/-- The coordinate rank equals the cardinality of its geometric generic points. -/
theorem FF.coordinate_finrank [IsLocalRing R] [PerfectField K] (X : FF R K) :
    Module.finrank R X.CoordinateRing = Nat.card X.Points := by
  let : Module.Free R X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  rw [← Module.finrank_baseChange (R := K)]
  exact X.genericCoordinates.toAlgEquiv.toLinearEquiv.finrank_eq.symm.trans
    (GaloisModule.finrank_equivariantFunctions K (AlgebraicClosure K) X.Points)

/-- The augmentation rank is one less than the generic group order. -/
theorem FF.augmentation_finrank [IsDomain R] [IsPrincipalIdealRing R]
    [IsLocalRing R] [PerfectField K] (X : FF R K) :
    1 + Module.finrank R X.augmentation = Nat.card X.Points := by
  let : Module.Free R X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  have h := X.augmentationSplit.finrank_eq
  rw [Module.finrank_prod, Module.finrank_self, X.coordinate_finrank] at h
  exact h.symm

end ThreeAdicPlan
