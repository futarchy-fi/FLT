/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianIdentityFiberGroup
public import FLT.Mazur.WeierstrassIdentityFiberOperations
public import Mathlib.CategoryTheory.Limits.Over

/-!
# The original embedded identity fiber as a commutative group scheme

The exact Cartesian identity fiber is given its constructed group structure
without changing its carrier, original inclusion or coefficient morphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace FLT.Mazur.WeierstrassIdentityFiber

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (E V : WeierstrassCurve R)
  (hE : IsUnit E.Δ) (hV : IsUnit V.Δ)
  (f : integralCurveGroup E hE ⟶ integralCurveGroup V hV)
  {H : Scheme.{u}} (i : H ⟶ integralCurve E)

/-- The original embedded fiber's inclusion in the category over the coefficient base. -/
def overInclusion : Over.mk (i ≫ integralCurveStructure E) ⟶ integralCurveOver E :=
  Over.homMk i rfl

/-- The original monomorphic inclusion remains monomorphic over the coefficient base. -/
instance overInclusion_mono [Mono i] : Mono (overInclusion E i) := by
  let _ : Mono (overInclusion E i).left := inferInstanceAs (Mono i)
  exact Over.mono_of_mono_left _

variable (h : IsPullback i (i ≫ integralCurveStructure E)
  f.hom.hom.hom.left (integralCurveZero V))

include h in
/-- The same Cartesian square holds in the category over the original coefficient base. -/
theorem over_isPullback :
    IsPullback (overInclusion E i) (toUnit (Over.mk (i ≫ integralCurveStructure E)))
      f.hom.hom.hom η[(integralCurveGroup V hV).X] :=
  IsPullback.of_map_of_faithful (Over.forget _) h

/-- The full original identity fiber carries the constructed commutative group operations. -/
@[instance_reducible] def fiberCommGrpObj [Mono i] :
    CommGrpObj (Over.mk (i ≫ integralCurveStructure E)) :=
  CartesianIdentityFiberGroup.commGrpObj f.hom.hom.hom (overInclusion E i)
    (toUnit _) (over_isPullback E V hE hV f i h)

/-- The original identity fiber bundled as a group, with exactly its original structure map. -/
def fiberGroup [Mono i] : CommGrp (Over (Spec (.of R))) := by
  let _ := fiberCommGrpObj E V hE hV f i h
  exact ⟨Over.mk (i ≫ integralCurveStructure E)⟩

/-- The bundled group has exactly the original embedded fiber as its carrier. -/
theorem fiberGroup_carrier [Mono i] :
    (fiberGroup E V hE hV f i h).X = Over.mk (i ≫ integralCurveStructure E) := rfl

/-- The original inclusion preserves the constructed group operations. -/
instance fiberGroup_inclusion_isMonHom [Mono i] :
    let _ := fiberCommGrpObj E V hE hV f i h
    let _ := integralCurveCommGrpObj E hE
    IsMonHom (overInclusion E i) := by
  let _ := integralCurveCommGrpObj E hE
  let _ := integralCurveCommGrpObj V hV
  exact CartesianIdentityFiberGroup.inclusion_isMonHom f.hom.hom.hom (overInclusion E i)
    (toUnit _) (over_isPullback E V hE hV f i h)

/-- The exact original inclusion as a morphism of commutative group schemes. -/
def fiberGroupInclusion [Mono i] : fiberGroup E V hE hV f i h ⟶ integralCurveGroup E hE :=
  ⟨Grp.ofHom (overInclusion E i)⟩

/-- The bundled group inclusion is exactly the original scheme inclusion. -/
theorem fiberGroupInclusion_left [Mono i] :
    (fiberGroupInclusion E V hE hV f i h).hom.hom.hom.left = i := rfl

end FLT.Mazur.WeierstrassIdentityFiber
