/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSelectorQuotient
public import FLT.Mazur.RelativeRelationSplitQuotient

/-!
# The constructed selector scheme represents the original invariant quotient

The equalizer construction identifies the full invariant locally ringed
space, not only its point set. Both the source projection and the original
relative structure map are retained by this structure-sheaf identification.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSelectorQuotient
open RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (r : A.left ⟶ D.left) (hr : r ≫ p.left = 𝟙 A.left)
  (hi : p.left ≫ r ≫ q.left = q.left ≫ r ≫ q.left)

/-- The constructed scheme carries the original ground morphism. -/
def relativeTarget : Over S := Over.mk (inclusion (q := q) r ≫ A.hom)

/-- The quotient morphism over the unchanged ground. -/
def relativeProjection : A ⟶ relativeTarget (q := q) r :=
  Over.homMk (projection r hr hi) (projection_ground r hr hi)

/-- The representative section over that same ground. -/
def relativeInclusion : relativeTarget (q := q) r ⟶ A :=
  Over.homMk (inclusion (q := q) r)

/-- The actual representative arrow is automatically a relative morphism. -/
def relativeSelector : A ⟶ D := Over.homMk r (by
  rw [← p.w, ← Category.assoc, hr, Category.id_comp])

/-- The relative projection coequalizes the complete original relation. -/
theorem relative_condition : p ≫ relativeProjection r hr hi = q ≫ relativeProjection r hr hi :=
  Over.OverMorphism.ext (condition r hr hi)

@[reassoc]
theorem relative_inclusion_projection :
    relativeInclusion (q := q) r ≫ relativeProjection r hr hi = 𝟙 _ :=
  Over.OverMorphism.ext (inclusion_projection r hr hi)

@[reassoc]
theorem relative_selector_fst : relativeSelector r hr ≫ p = 𝟙 A :=
  Over.OverMorphism.ext hr

@[reassoc]
theorem relative_selector_snd : relativeSelector r hr ≫ q =
    relativeProjection r hr hi ≫ relativeInclusion (q := q) r :=
  Over.OverMorphism.ext (projection_inclusion r hr hi).symm

/-- The original invariant quotient is the constructed scheme, including its structure sheaf. -/
def invariantIso : invariantLocallyRingedSpace e ≅ (target (q := q) r).toLocallyRingedSpace :=
  splitInvariantQuotientIso e (relativeProjection r hr hi) (relativeInclusion (q := q) r)
    (relative_condition r hr hi) (relative_inclusion_projection r hr hi)
    (relativeSelector r hr) (relative_selector_fst r hr) (relative_selector_snd r hr hi)

/-- The structure-sheaf comparison preserves the actual constructed source projection. -/
@[reassoc]
theorem invariantIso_projection :
    invariantLocallyRingedProjection e ≫ (invariantIso e r hr hi).hom =
      (projection r hr hi).toLRSHom :=
  splitInvariantQuotientIso_projection e (relativeProjection r hr hi)
    (relativeInclusion (q := q) r) (relative_condition r hr hi)
    (relative_inclusion_projection r hr hi) (relativeSelector r hr)
    (relative_selector_fst r hr) (relative_selector_snd r hr hi)

/-- The structure-sheaf identification also retains the literal original ground map. -/
theorem invariantIso_ground : (invariantIso e r hr hi).hom ≫
    (inclusion (q := q) r ≫ A.hom).toLRSHom = invariantLocallyRingedBaseMap e :=
  splitInvariantQuotientIso_baseMap e (relativeProjection r hr hi)
    (relativeInclusion (q := q) r) (relative_condition r hr hi)
    (relative_inclusion_projection r hr hi) (relativeSelector r hr)
    (relative_selector_fst r hr) (relative_selector_snd r hr hi)

end FLT.Mazur.SchemeRelationSelectorQuotient
