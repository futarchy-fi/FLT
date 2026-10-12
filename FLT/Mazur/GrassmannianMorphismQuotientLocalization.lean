/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismEffectiveRelation

/-!
# Actual localization maps for the recovered global quotient

Local effectiveness identifies the localization of the original quotient with
the full recovered chart quotient. These are module isomorphisms, not just
isomorphisms of residue fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)

/-- The localized original quotient is the entire recovered local quotient. -/
def ambientMorphismQuotientLocalEquiv (q : AmbientMorphismCoverIndex f) :
    ((Localization.Away q.2.val ⊗[R] M) ⧸
      (ambientMorphismRelation f hf).localized' (Localization.Away q.2.val)
        (.powers q.2.val) (AlgebraTensorModule.rTensor R M
          (Algebra.linearMap A (Localization.Away q.2.val)))) ≃ₗ[Localization.Away q.2.val]
    ((Localization.Away q.2.val ⊗[R] M) ⧸
      (ambientMorphismLocalPoint f hf q).val.toSubmodule) :=
  Submodule.quotEquivOfEq _ _ (ambientMorphismRelation_localized_eq f hf q)

/-- The original global quotient maps to each actual recovered quotient by localization. -/
def ambientMorphismQuotientLocalization (q : AmbientMorphismCoverIndex f) :
    ((A ⊗[R] M) ⧸ ambientMorphismRelation f hf) →ₗ[A]
      ((Localization.Away q.2.val ⊗[R] M) ⧸
        (ambientMorphismLocalPoint f hf q).val.toSubmodule) :=
  (ambientMorphismQuotientLocalEquiv f hf q).restrictScalars A |>.toLinearMap.comp
    ((ambientMorphismRelation f hf).toLocalizedQuotient' (Localization.Away q.2.val)
      (.powers q.2.val) (AlgebraTensorModule.rTensor R M
        (Algebra.linearMap A (Localization.Away q.2.val))))

/-- The quotient map has the localization universal property, including its kernel. -/
instance ambientMorphismQuotientLocalization_isLocalized (q : AmbientMorphismCoverIndex f) :
    IsLocalizedModule (.powers q.2.val) (ambientMorphismQuotientLocalization f hf q) :=
  IsLocalizedModule.of_linearEquiv _ _
    ((ambientMorphismQuotientLocalEquiv f hf q).restrictScalars A)

/-- The localized quotient map takes every original vector to its actual local class. -/
theorem ambientMorphismQuotientLocalization_mk (q : AmbientMorphismCoverIndex f)
    (x : A ⊗[R] M) :
    ambientMorphismQuotientLocalization f hf q (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (AlgebraTensorModule.rTensor R M
        (Algebra.linearMap A (Localization.Away q.2.val)) x) := by
  simp only [ambientMorphismQuotientLocalization, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    Submodule.toLocalizedQuotient'_mk, ambientMorphismQuotientLocalEquiv,
    Submodule.quotEquivOfEq_mk]

/-- The local quotient is the actual tensor base change of the original global quotient. -/
def ambientMorphismQuotientBaseChange (q : AmbientMorphismCoverIndex f) :
    Localization.Away q.2.val ⊗[A] ((A ⊗[R] M) ⧸ ambientMorphismRelation f hf) ≃ₗ[
      Localization.Away q.2.val]
    ((Localization.Away q.2.val ⊗[R] M) ⧸
      (ambientMorphismLocalPoint f hf q).val.toSubmodule) :=
  (IsLocalizedModule.isBaseChange (.powers q.2.val) (Localization.Away q.2.val)
    (ambientMorphismQuotientLocalization f hf q)).equiv

end FLT.Mazur.GrassmannianChart
