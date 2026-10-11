/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModifiedSmoothAffineRefinement

/-!
# Original output coordinates on the complete modified smooth refinement

Each member of the actual cover comes with an output chart and its ring map.
The ring map presents exactly the original action, including the output
charts at infinity. No lifted modification action is assumed here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R A : Type u} [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (c : Spec (.of A) ⟶ integralCurve W)

/-- The original output chart attached to a member of the actual refinement. -/
def modifiedSmoothOutputIndex (i : (modifiedSmoothAffineCover W c).I₀) : Fin 3 := i.1.down

/-- The original output projection supplied by the pullback defining the cover. -/
def modifiedSmoothOutputProjection (i : (modifiedSmoothAffineCover W c).I₀) :
    Spec ((modifiedSmoothAffineCover W c).X i) ⟶
      Spec (.of (Coordinate W (modifiedSmoothOutputIndex W c i))) :=
  ((modifiedSmoothOutputCover W c).X i.1).affineCover.f i.2 ≫ pullback.snd _ _

/-- The output projection contracts to the actual original action on the cover member. -/
@[reassoc] theorem modifiedSmoothOutputProjection_addition
    (i : (modifiedSmoothAffineCover W c).I₀) :
    modifiedSmoothOutputProjection W c i ≫
        integralCurveChart W (modifiedSmoothOutputIndex W c i) =
      (modifiedSmoothAffineCover W c).f i ≫ modifiedSmoothAffineAddition W c := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => ((modifiedSmoothOutputCover W c).X i.1).affineCover.f i.2 ≫ t)
      (pullback.condition (f := modifiedSmoothAffineAddition W c)
        (g := (integralCurveOpenCover W).f i.1)).symm).trans (Category.assoc _ _ _).symm)

/-- The actual ring map of the original output in its assigned affine chart. -/
def modifiedSmoothOutputHom (i : (modifiedSmoothAffineCover W c).I₀) :
    Coordinate W (modifiedSmoothOutputIndex W c i) →+*
      (modifiedSmoothAffineCover W c).X i :=
  affineChartRingHom (modifiedSmoothOutputProjection W c i)

/-- Extracting the output coordinates retains the original scheme projection. -/
@[simp] theorem modifiedSmoothOutputHom_spec (i : (modifiedSmoothAffineCover W c).I₀) :
    Spec.map (CommRingCat.ofHom (modifiedSmoothOutputHom W c i)) =
      modifiedSmoothOutputProjection W c i := affineChartRingHom_spec _

/-- The output coordinates present the original sum of the actual pair on every cover member. -/
theorem modifiedSmoothOutputHom_addition (i : (modifiedSmoothAffineCover W c).I₀) :
    Spec.map (CommRingCat.ofHom (modifiedSmoothOutputHom W c i)) ≫
        integralCurveChart W (modifiedSmoothOutputIndex W c i) =
      leftSmoothPointAddition W (modifiedSmoothAffineParameter W c i)
        (modifiedSmoothAffineProjection W c i ≫ c)
        (modifiedSmoothAffineParameter_structure W c i) := by
  rw [modifiedSmoothOutputHom_spec, modifiedSmoothOutputProjection_addition,
    modifiedSmoothAffineCover_addition]

/-- Every point of the entire smooth-input product belongs to an actual affine presentation. -/
theorem modifiedSmoothAffineCover_covers (z : modifiedSmoothAffineProduct W c) :
    ∃ (i : (modifiedSmoothAffineCover W c).I₀)
      (x : Spec ((modifiedSmoothAffineCover W c).X i)),
      (modifiedSmoothAffineCover W c).f i x = z :=
  (modifiedSmoothAffineCover W c).openCover.exists_eq z

/-- Output coordinates transported to a specified original chart. -/
def modifiedSmoothOutputHomAt (i : (modifiedSmoothAffineCover W c).I₀)
    (j : Fin 3) (h : modifiedSmoothOutputIndex W c i = j) :
    Coordinate W j →+* (modifiedSmoothAffineCover W c).X i :=
  h ▸ modifiedSmoothOutputHom W c i

/-- Transporting the chart index retains the original action presentation. -/
theorem modifiedSmoothOutputHomAt_addition (i : (modifiedSmoothAffineCover W c).I₀)
    (j : Fin 3) (h : modifiedSmoothOutputIndex W c i = j) :
    Spec.map (CommRingCat.ofHom (modifiedSmoothOutputHomAt W c i j h)) ≫
        integralCurveChart W j =
      leftSmoothPointAddition W (modifiedSmoothAffineParameter W c i)
        (modifiedSmoothAffineProjection W c i ≫ c)
        (modifiedSmoothAffineParameter_structure W c i) := by
  subst j
  exact modifiedSmoothOutputHom_addition W c i

end FLT.Mazur.WeierstrassIntegralChart
