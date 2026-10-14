/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfTargetOpen

/-!
# Constructed fppf regions retain their original coefficient base

The open-image factorization is promoted to schemes over the original base.
Its Cartesian square preserves the whole source and both coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeFppfTargetOpen
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A T : Over S} (w : A ⟶ T)
  [LocallyOfFinitePresentation w.left]

/-- The actual open in the unchanged relative target. -/
def target : Over S := Over.mk ((SchemeFppfTargetOpen.locus w.left).ι ≫ T.hom)

/-- The complete source above the constructed flat region, over the original base. -/
def source : Over S :=
  Over.mk (pullback.fst w.left (SchemeFlatTargetOpen.locus w.left).ι ≫ A.hom)

/-- The original target inclusion, including the unchanged structure morphism. -/
def toTarget : target w ⟶ T := Over.homMk (SchemeFppfTargetOpen.locus w.left).ι

/-- The original source restriction, with no selected fiber branch. -/
def toSource : source w ⟶ A :=
  Over.homMk (pullback.fst w.left (SchemeFlatTargetOpen.locus w.left).ι)

/-- The actual fppf projection, as a relative scheme morphism. -/
def projection : source w ⟶ target w :=
  Over.homMk (SchemeFppfTargetOpen.projection w.left) (by
    change SchemeFppfTargetOpen.projection w.left ≫
      (SchemeFppfTargetOpen.locus w.left).ι ≫ T.hom = _
    rw [← Category.assoc, SchemeFppfTargetOpen.projection_ι]
    change (pullback.snd _ _ ≫ (SchemeFlatTargetOpen.locus w.left).ι) ≫ T.hom = _
    rw [← pullback.condition, Category.assoc, w.w]
    rfl)

/-- The full square commutes over the actual base. -/
@[reassoc]
theorem condition : toSource w ≫ w = projection w ≫ toTarget w := by
  apply Over.OverMorphism.ext
  exact (pullback.condition (f := w.left)).trans
    (SchemeFppfTargetOpen.projection_ι w.left).symm

/-- Flatness comes from the constructed region rather than an original projection hypothesis. -/
instance projection_flat : Flat (projection w).left :=
  SchemeFppfTargetOpen.projection_flat w.left

instance projection_surjective : Surjective (projection w).left :=
  SchemeFppfTargetOpen.projection_surjective w.left

instance projection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (projection w).left :=
  SchemeFppfTargetOpen.projection_locallyOfFinitePresentation w.left

instance toTarget_isOpenImmersion : IsOpenImmersion (toTarget w).left :=
  inferInstanceAs (IsOpenImmersion (SchemeFppfTargetOpen.locus w.left).ι)

instance toSource_isOpenImmersion : IsOpenImmersion (toSource w).left :=
  inferInstanceAs (IsOpenImmersion (pullback.fst _ _))

/-- The underlying square is Cartesian, retaining the entire original scheme structure. -/
theorem isPullback : IsPullback (toSource w).left (projection w).left
    w.left (toTarget w).left := SchemeFppfTargetOpen.isPullback w.left

end FLT.Mazur.RelativeFppfTargetOpen
