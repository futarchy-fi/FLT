/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
public import FLT.Mazur.WeierstrassCoefficientShearRootChange

/-!
# Composition of actual coefficient specializations with chosen-root changes

The complete equation models form a contravariant system in coefficient algebras.
Identity coefficient maps recover the independently defined whole-model root change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T U : Type u) [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]
  (r : S) (v : T) (w : U) (j : ℕ) (hj : j ≤ n)
  (f : S →ₐ[R] T) (g : T →ₐ[R] U)

/-- Successive coefficient specializations agree on the whole model, including its nodes. -/
@[reassoc] theorem coefficientShearSpecialization_comp :
    coefficientShearSpecialization hπ data T U v w j hj g ≫
        coefficientShearSpecialization hπ data S T r v j hj f =
      coefficientShearSpecialization hπ data S U r w j hj (g.comp f) := by
  apply (coefficientShearGlued_isPullback hπ data S r j hj).hom_ext
  · simp only [Category.assoc, coefficientShearSpecialization_structure,
      coefficientShearSpecialization_structure_assoc]
    rw [← Spec.map_comp]
    rfl
  · rw [Category.assoc, coefficientShearSpecialization_projection,
      coefficientShearSpecialization_projection, coefficientShearSpecialization_projection]

/-- Identity coefficient specialization changes only the actual chosen shear parameter. -/
theorem coefficientShearSpecialization_id_rootChange (t : S) :
    coefficientShearSpecialization hπ data S S t r j hj (AlgHom.id R S) =
      (coefficientShearRootChange hπ data S r t j hj).hom := by
  apply (coefficientShearGlued_isPullback hπ data S t j hj).hom_ext
  · rw [coefficientShearSpecialization_structure, coefficientShearRootChange_structure]
    change _ ≫ Spec.map (𝟙 _) = _
    rw [Spec.map_id, Category.comp_id]
  · rw [coefficientShearSpecialization_projection, coefficientShearRootChange_projection]

/-- Specializing the identity coefficient map at the same root gives the identity morphism. -/
theorem coefficientShearSpecialization_id :
    coefficientShearSpecialization hπ data S S r r j hj (AlgHom.id R S) = 𝟙 _ := by
  rw [coefficientShearSpecialization_id_rootChange]
  exact (coefficientShearGluedIso hπ data S r j hj).hom_inv_id

/-- A source-root change commutes with the complete original coefficient specialization. -/
@[reassoc] theorem coefficientShearSpecialization_sourceRoot (v' : T) :
    (coefficientShearRootChange hπ data T v v' j hj).hom ≫
        coefficientShearSpecialization hπ data S T r v' j hj f =
      coefficientShearSpecialization hπ data S T r v j hj f := by
  rw [← coefficientShearSpecialization_id_rootChange,
    coefficientShearSpecialization_comp]
  rfl

/-- A target-root change preserves the same original coefficient and model projections. -/
@[reassoc] theorem coefficientShearSpecialization_targetRoot (r' : S) :
    coefficientShearSpecialization hπ data S T r v j hj f ≫
        (coefficientShearRootChange hπ data S r r' j hj).hom =
      coefficientShearSpecialization hπ data S T r' v j hj f := by
  rw [← coefficientShearSpecialization_id_rootChange,
    coefficientShearSpecialization_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
