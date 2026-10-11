/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentKernelPair
public import FLT.Mazur.RelativeRelationOrbit

/-!
# The actual relative relation of multiplicative affine descent

Keep the original coaction and coefficient-inclusion endpoints as morphisms
over the original base. Their proved kernel-pair square constructs the internal
equivalence relation; no effective quotient data is added as an assumption.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineAlgebraDescent
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B)

/-- The constructed descended scheme with its original structural map. -/
def relativeTarget : Over (Spec (.of R)) := Over.mk (schemeBase D)

/-- The original coefficient scheme viewed over the original base. -/
def relativeSource : Over (Spec (.of R)) :=
  Over.mk (schemeProjection D ≫ schemeBase D)

/-- The original tensor-overlap scheme viewed over the original base. -/
def relativeOverlap : Over (Spec (.of R)) :=
  Over.mk (overlapFst D ≫ schemeProjection D ≫ schemeBase D)

/-- The original coefficient projection as a relative scheme map. -/
def relativeProjection : relativeSource D ⟶ relativeTarget D :=
  Over.homMk (schemeProjection D)

/-- The coaction endpoint, retaining its original relative structure. -/
def relativeFst : relativeOverlap D ⟶ relativeSource D := Over.homMk (overlapFst D)

/-- The coefficient-inclusion endpoint, with the same original relative structure. -/
def relativeSnd : relativeOverlap D ⟶ relativeSource D :=
  Over.homMk (overlapSnd (R := R) (S := S) (B := B)) (by
    change _ ≫ (schemeProjection D ≫ schemeBase D) = _
    rw [← Category.assoc, ← overlap_condition, Category.assoc]
    rfl)

/-- The relative source structural map is exactly the original coefficient algebra map. -/
theorem relativeSource_hom : (relativeSource D).hom =
    Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  change schemeProjection D ≫ schemeBase D = _
  rw [schemeProjection, schemeBase, ← Spec.map_comp]
  rfl

/-- The original affine overlap remains the full kernel pair over the original base. -/
theorem relative_isPullback [Module.Flat R S] :
    IsPullback (relativeFst D) (relativeSnd D) (relativeProjection D) (relativeProjection D) :=
  IsPullback.of_map_of_faithful (Over.forget _) (overlap_isPullback D)

/-- The full coaction overlap constructs an internal relative equivalence relation. -/
def relativeEquivalenceRelation [Module.Flat R S] :
    CategoryTheory.EquivalenceRelation (relativeFst D) (relativeSnd D) :=
  IsKernelPair.equivalenceRelation (relativeProjection D)
    (relativeFst D) (relativeSnd D) (pullback.isLimit _ _) (relative_isPullback D)

instance schemeProjection_quasiCompact : QuasiCompact (schemeProjection D) :=
  inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (invariants D).val.toRingHom)))

end FLT.Mazur.AffineAlgebraDescent
