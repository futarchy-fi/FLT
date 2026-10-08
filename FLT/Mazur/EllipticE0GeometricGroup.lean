/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticE0SectionEquiv
public import FLT.Mazur.WeierstrassSmoothProjectiveGroup

/-!
# The original E₀ subgroup is the actual smooth integral section group

Generic restriction is injective and commutes with the constructed geometric
addition. The classical smooth field-point comparison therefore upgrades the
section equivalence to an additive equivalence with the actual group scheme's
section group, including at bad reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory
open scoped MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Generic restriction is injective on actual smooth integral sections. -/
theorem smoothSectionGeneric_injective : Function.Injective (smoothSectionGeneric A W) := by
  intro s t h
  obtain ⟨P, rfl⟩ := e0ToSmoothSection_surjective A W s
  obtain ⟨Q, rfl⟩ := e0ToSmoothSection_surjective A W t
  rw [e0ToSmoothSection_generic, e0ToSmoothSection_generic] at h
  have he : P = Q := Subtype.ext (projectiveToSmoothOver_injective W h)
  rw [he]

/-- Generic restriction respects the actual smooth geometric addition. -/
theorem smoothSectionGeneric_addition (s t : smoothIntegralSection A W) :
    smoothSectionGeneric A W (lift s t ≫ integralSmoothOverAddition W) =
      lift (smoothSectionGeneric A W s) (smoothSectionGeneric A W t) ≫
        integralSmoothOverAddition W := by
  let g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⟶
      Over.mk (𝟙 (Spec (.of A))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) (Category.comp_id _)
  change g ≫ (lift s t ≫ integralSmoothOverAddition W) =
    lift (g ≫ s) (g ≫ t) ≫ integralSmoothOverAddition W
  rw [← Category.assoc, comp_lift]

/-- The original arithmetic subgroup addition agrees with the constructed geometric addition. -/
theorem e0ToSmoothSection_add (P Q : ellipticE0 A W) :
    e0ToSmoothSection A W (P + Q) =
      lift (e0ToSmoothSection A W P) (e0ToSmoothSection A W Q) ≫
        integralSmoothOverAddition W := by
  apply smoothSectionGeneric_injective A W
  rw [smoothSectionGeneric_addition, e0ToSmoothSection_generic,
    e0ToSmoothSection_generic, e0ToSmoothSection_generic]
  exact projectiveToSmoothOver_add W P.val Q.val

/-- The integral sections with the actual previously constructed commutative group law. -/
def smoothGroupIntegralSections : CommGrpCat :=
  CommGrpCat.of (Over.mk (𝟙 (Spec (.of A))) ⟶ (integralSmoothGroup W).X)

/-- Arithmetic E₀ is the actual geometric smooth section group, with its existing operations. -/
def e0SmoothSectionAddEquiv :
    ellipticE0 A W ≃+ Additive (smoothGroupIntegralSections A W) where
  toFun P := Additive.ofMul (e0ToSmoothSection A W P)
  invFun s := (e0SmoothSectionEquiv A W).symm s.toMul
  left_inv := (e0SmoothSectionEquiv A W).left_inv
  right_inv := (e0SmoothSectionEquiv A W).right_inv
  map_add' := e0ToSmoothSection_add A W

/-- The group equivalence keeps the same underlying integral section of each original point. -/
theorem e0SmoothSectionAddEquiv_apply (P : ellipticE0 A W) :
    (e0SmoothSectionAddEquiv A W P).toMul = e0ToSmoothSection A W P := rfl

end FLT.Mazur.WeierstrassIntegralChart
