/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterPowers

/-!
# Model morphisms on the actual character lines

Generic scalar compatibility implies integral compatibility by faithfulness.
Coordinate pullback then preserves each actual integral character space.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open CharacterProjector

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K] [Field F]
  {X Y : FF R K} (f : ModelHom X Y)
  (sx : F → ModelHom X X) (sy : F → ModelHom Y Y)
  (hx1 : sx 1 = BialgHom.id R X.CoordinateRing)
  (hy1 : sy 1 = BialgHom.id R Y.CoordinateRing)
  (hxm : ∀ a b, sx (a * b) = (sx b).comp (sx a))
  (hym : ∀ a b, sy (a * b) = (sy b).comp (sy a))
  (hcomm : ∀ a, f.comp (sy a) = (sx a).comp f)

/-- Coordinate pullback restricts to the actual integral character lines. -/
def ModelHom.integralCharacterMap (χ : Fˣ →* Rˣ) :
    Y.integralCharacter sy hy1 hym χ →ₗ[R] X.integralCharacter sx hx1 hxm χ where
  toFun v := ⟨⟨f (v.val : Y.CoordinateRing), by
    change Coalgebra.counit (f (v.val : Y.CoordinateRing)) = 0
    rw [CoalgHomClass.counit_comp_apply]
    exact v.val.property⟩, by
    apply (mem_eigenspace_iff _ _ _).mpr
    intro u
    apply Subtype.ext
    change sx u (f (v.val : Y.CoordinateRing)) = (χ u : R) • f (v.val : Y.CoordinateRing)
    have h := DFunLike.congr_fun (hcomm u) (v.val : Y.CoordinateRing)
    change f (sy u (v.val : Y.CoordinateRing)) = sx u (f (v.val : Y.CoordinateRing)) at h
    rw [← h, Y.integralCharacter_scalar sy hy1 hym χ v u, map_smul]⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add f _ _
  map_smul' r a := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul f r _

variable [PerfectField K] [IsFractionRing R K]

/-- A generically surjective point map is injective on integral coordinates. -/
theorem ModelHom.injective_of_generic_surjective (hf : Function.Surjective (genericHom f)) :
    Function.Injective f := by
  intro a b hab
  apply Y.characterCoordinates_injective
  ext y
  obtain ⟨x, rfl⟩ := hf y
  rw [← f.characterCoordinates_apply, ← f.characterCoordinates_apply, hab]

variable [Module F X.Points] [Module F Y.Points]
  (hsx : ∀ a x, genericHom (sx a) x = a • x)
  (hsy : ∀ a y, genericHom (sy a) y = a • y)
  (hf : ∀ (a : F) x, genericHom f (a • x) = a • genericHom f x)

include hsx hsy hf in
/-- Compatibility of generic scalar actions forces compatibility of the integral lifts. -/
theorem ModelHom.scalar_compatible (a : F) : f.comp (sy a) = (sx a).comp f := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, hsx, hsy, hf]

end ThreeAdicPlan
