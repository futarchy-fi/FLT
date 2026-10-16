/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFunctionGroundChange
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Full relation diagrams on invariant open source domains

Restricting the original relation at its first endpoint retains every arrow
above an invariant source open. Both endpoints and the coefficient structure
are constructed as scheme maps; the source and relation remain unchanged there.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.InvariantOpenRelationDiagram
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{0}} {A D : Over S} (p q : D ⟶ A)
  (U : A.left.Opens) (hU : p.left ⁻¹ᵁ U = q.left ⁻¹ᵁ U)

/-- The actual open source over the original coefficient scheme. -/
def source : Over S := Over.mk (U.ι ≫ A.hom)

/-- The entire original relation above the invariant open. -/
def relation : Over S := Over.mk ((p.left ⁻¹ᵁ U).ι ≫ D.hom)

/-- Inclusion of the actual open source into the original source. -/
def sourceInclusion : source U ⟶ A := Over.homMk U.ι

/-- Inclusion retains every original arrow above the open source. -/
def relationInclusion : relation p U ⟶ D := Over.homMk (p.left ⁻¹ᵁ U).ι

/-- The first endpoint on the full open relation. -/
def fst : relation p U ⟶ source U :=
  Over.homMk (p.left.resLE U _ le_rfl) (by
    change _ ≫ U.ι ≫ A.hom = _
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w p]
    rfl)

/-- Invariance constructs the second endpoint on the same relation scheme. -/
def snd : relation p U ⟶ source U :=
  Over.homMk (q.left.resLE U _ hU.le) (by
    change _ ≫ U.ι ≫ A.hom = _
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w q]
    rfl)

/-- The first endpoint square is the actual open base-change square. -/
theorem fst_isPullback : IsPullback (relationInclusion p U).left (fst p U).left
    p.left (sourceInclusion U).left := by
  change IsPullback (p.left ⁻¹ᵁ U).ι (p.left.resLE U _ le_rfl) p.left U.ι
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict p.left U).flip

/-- The first endpoint square commutes over the original coefficient scheme. -/
@[reassoc]
theorem inclusion_fst : relationInclusion p U ≫ p = fst p U ≫ sourceInclusion U := by
  apply Over.OverMorphism.ext
  exact (fst_isPullback p U).w

/-- The second endpoint square commutes over the original coefficient scheme. -/
@[reassoc]
theorem inclusion_snd :
    relationInclusion p U ≫ q = snd p q U hU ≫ sourceInclusion U := by
  apply Over.OverMorphism.ext
  exact (Scheme.Hom.resLE_comp_ι q.left hU.le).symm

instance sourceInclusion_open : IsOpenImmersion (sourceInclusion U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

instance relationInclusion_open : IsOpenImmersion (relationInclusion p U).left :=
  inferInstanceAs (IsOpenImmersion (p.left ⁻¹ᵁ U).ι)

instance source_separated [A.left.IsSeparated] : (source U).left.IsSeparated := by
  refine ⟨?_⟩
  rw [← terminal.comp_from (sourceInclusion U).left]
  infer_instance

instance relation_separated [D.left.IsSeparated] : (relation p U).left.IsSeparated := by
  refine ⟨?_⟩
  rw [← terminal.comp_from (relationInclusion p U).left]
  infer_instance

end FLT.Mazur.InvariantOpenRelationDiagram
