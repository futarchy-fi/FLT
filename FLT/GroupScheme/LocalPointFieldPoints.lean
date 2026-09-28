/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalPointField
public import FLT.GroupScheme.KummerPoints

/-!
# All integral points and the full point field

Every geometric point of a finite flat three-adic model is integral over its
full point field. Conversely, any finite extension realizing every geometric
point contains an isomorphic copy of that full field. The argument uses the
kernel of the action on all points, rather than the values of a single point.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable (M : FF ℤ_[3] ℚ_[3])
variable (E : Type) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E]

/-- An integral point, viewed geometrically through a specified field embedding. -/
def FF.geometricIntegralPoint (j : E →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3])
    (u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E) :
    ℚ_[3] ⊗[ℤ_[3]] M.CoordinateRing →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3] :=
  Algebra.TensorProduct.liftEquivRight ℤ_[3] ℚ_[3] _ _
    ((j.restrictScalars ℤ_[3]).comp ((integralClosure ℤ_[3] E).val.comp u))

/-- The geometric point takes a model coordinate to its embedded integral value. -/
@[simp] theorem FF.geometricIntegralPoint_tmul
    (j : E →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3])
    (u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E) (a : M.CoordinateRing) :
    M.geometricIntegralPoint E j u (1 ⊗ₜ[ℤ_[3]] a) = j (u a : E) := by
  simp [FF.geometricIntegralPoint]

/-- Passing to geometric points through a field embedding is injective. -/
theorem FF.geometricIntegralPoint_injective
    (j : E →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3]) :
    Function.Injective (M.geometricIntegralPoint E j) := by
  intro u v h
  ext a
  apply j.injective
  change j (u a : E) = j (v a : E)
  simpa only [M.geometricIntegralPoint_tmul] using
    AlgHom.congr_fun h (1 ⊗ₜ[ℤ_[3]] a)

/-- Every geometric point is integral over the full point field. -/
theorem FF.geometricIntegralPoint_localPointField_surjective :
    Function.Surjective
      (M.geometricIntegralPoint (LocalPointField M) (LocalPointField M).val) := by
  intro f
  let g : ℚ_[3] ⊗[ℤ_[3]] M.CoordinateRing →ₐ[ℚ_[3]] LocalPointField M :=
    f.codRestrict (LocalPointField M).toSubalgebra (M.pointValue_mem_localPointField f)
  let u : M.CoordinateRing →ₐ[ℤ_[3]] LocalPointField M :=
    Bialgebra.restrictPoints ℤ_[3] ℚ_[3] (LocalPointField M) M.CoordinateRing g
  let v : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers (LocalPointField M) :=
    u.codRestrict (integralClosure ℤ_[3] (LocalPointField M))
      (fun a ↦ (Algebra.IsIntegral.isIntegral (R := ℤ_[3]) a).map u)
  refine ⟨v, ?_⟩
  apply (Bialgebra.restrictPoints ℤ_[3] ℚ_[3] (AlgebraicClosure ℚ_[3])
    M.CoordinateRing).injective
  ext a
  exact M.geometricIntegralPoint_tmul (LocalPointField M) (LocalPointField M).val v a

/-- Full point-field integral points are exactly the geometric points. -/
def FF.localPointFieldIntegralPointsEquiv :
    (M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers (LocalPointField M)) ≃
      (ℚ_[3] ⊗[ℤ_[3]] M.CoordinateRing →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3]) :=
  Equiv.ofBijective _ ⟨M.geometricIntegralPoint_injective _ _,
    M.geometricIntegralPoint_localPointField_surjective⟩

/-- If an intermediate field contains all geometric coordinate values, it
contains the full point field. No one point is required to generate it. -/
theorem FF.localPointField_le_of_pointValues (F : IntermediateField ℚ_[3]
    (AlgebraicClosure ℚ_[3]))
    (hF : ∀ (f : ℚ_[3] ⊗[ℤ_[3]] M.CoordinateRing →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3])
      (a : ℚ_[3] ⊗[ℤ_[3]] M.CoordinateRing), f a ∈ F) :
    LocalPointField M ≤ F := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup F]
  apply IntermediateField.fixedField_le
  intro σ hσ
  rw [M.mem_pointActionKernel]
  intro x
  obtain ⟨f, rfl⟩ := M.points_bijective.2 x
  rw [← map_smul]
  apply congrArg M.points
  change σ.toAlgHom.comp f.toMul = f.toMul
  apply AlgHom.ext
  intro a
  exact (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ _ (hF f.toMul a)

/-- Realizing every geometric point over an extension realizes its full point
field inside the image of any chosen embedding of that extension. -/
theorem FF.localPointField_le_fieldRange_of_integralPoints
    (j : E →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3])
    (hj : Function.Surjective (M.geometricIntegralPoint E j)) :
    LocalPointField M ≤ j.fieldRange := by
  apply M.localPointField_le_of_pointValues
  intro f a
  obtain ⟨u, rfl⟩ := hj f
  let g : ℚ_[3] ⊗[ℤ_[3]] M.CoordinateRing →ₐ[ℚ_[3]] E :=
    Algebra.TensorProduct.liftEquivRight ℤ_[3] ℚ_[3] _ _
      ((integralClosure ℤ_[3] E).val.comp u)
  have he : M.geometricIntegralPoint E j u = j.comp g := by
    apply (Bialgebra.restrictPoints ℤ_[3] ℚ_[3] (AlgebraicClosure ℚ_[3])
      M.CoordinateRing).injective
    ext b
    simp [FF.geometricIntegralPoint, Bialgebra.restrictPoints, g]
  rw [he]
  exact ⟨g a, rfl⟩

/-- Realizing all integral geometric points yields an embedding of the full
point field, even when no individual point generates that field. -/
theorem FF.nonempty_localPointField_algHom_of_integralPoints
    (j : E →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3])
    (hj : Function.Surjective (M.geometricIntegralPoint E j)) :
    Nonempty (LocalPointField M →ₐ[ℚ_[3]] E) :=
  ⟨j.equivFieldRange.symm.toAlgHom.comp
    (IntermediateField.inclusion (M.localPointField_le_fieldRange_of_integralPoints E j hj))⟩

end ThreeAdicPlan
