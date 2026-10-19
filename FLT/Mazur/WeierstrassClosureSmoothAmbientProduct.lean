/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureSmoothPart
public import FLT.Mazur.WeierstrassSmoothGroupOperations

/-!
# The actual ambient product of the smooth kernel intersection

Both original smooth inclusions induce the actual fiber-product morphism into
the integral smooth group. Its ambient sum remains over the original base.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K)))

local notation "s" => genericClosureSmoothStructure W i
local notation "j" => genericClosureSmoothInclusion W i

/-- The actual product inclusion into the original smooth ambient group. -/
def genericClosureSmoothAmbientPair : pullback s s ⟶ smoothFactorProduct W :=
  pullback.lift (pullback.fst s s ≫ j) (pullback.snd s s ≫ j) (by
    simp only [Category.assoc, genericClosureSmoothInclusion_structure]
    exact pullback.condition)

/-- The first ambient input is the original smooth inclusion. -/
@[reassoc] theorem genericClosureSmoothAmbientPair_fst :
    genericClosureSmoothAmbientPair W i ≫ pullback.fst _ _ = pullback.fst s s ≫ j :=
  pullback.lift_fst _ _ _

/-- The second ambient input is the original smooth inclusion. -/
@[reassoc] theorem genericClosureSmoothAmbientPair_snd :
    genericClosureSmoothAmbientPair W i ≫ pullback.snd _ _ = pullback.snd s s ≫ j :=
  pullback.lift_snd _ _ _

/-- The original smooth inclusion is a morphism over the original integral base. -/
def genericClosureSmoothOverInclusion : Over.mk s ⟶ integralSmoothOver W :=
  Over.homMk j (genericClosureSmoothInclusion_structure W i)

/-- The original smooth inclusion remains monomorphic over the original integral base. -/
instance genericClosureSmoothOverInclusion_mono : Mono (genericClosureSmoothOverInclusion W i) := by
  let _ : Mono (genericClosureSmoothOverInclusion W i).left := inferInstanceAs (Mono j)
  exact Over.mono_of_mono_left _

/-- The categorical product of the original inclusions is the actual ambient pair. -/
theorem genericClosureSmoothOverInclusion_tensor :
    (genericClosureSmoothOverInclusion W i ⊗ₘ genericClosureSmoothOverInclusion W i).left =
      genericClosureSmoothAmbientPair W i := by
  apply pullback.hom_ext
  · exact (Over.tensorHom_left_fst _ _ _ _).trans (genericClosureSmoothAmbientPair_fst W i).symm
  · exact (Over.tensorHom_left_snd _ _ _ _).trans (genericClosureSmoothAmbientPair_snd W i).symm

/-- The actual ambient addition remains over the original coefficient base. -/
@[reassoc] theorem genericClosureSmoothAmbientPair_addition_structure :
    (genericClosureSmoothAmbientPair W i ≫ smoothFactorAddition W) ≫
      integralSmoothStructure W = pullback.fst s s ≫ s := by
  rw [Category.assoc, smoothFactorAddition_structure, ← Category.assoc,
    genericClosureSmoothAmbientPair_fst, Category.assoc, genericClosureSmoothInclusion_structure]

end FLT.Mazur.WeierstrassIntegralChart
