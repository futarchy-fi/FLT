/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# Zero and inverse on an exact Cartesian identity fiber

The original embedded fiber of a group morphism acquires its own zero and inverse
by its pullback property. No replacement of its carrier or inclusion is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.WeierstrassIdentityFiber

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (E V : WeierstrassCurve R)
  (hE : IsUnit E.Δ) (hV : IsUnit V.Δ)
  (f : integralCurveGroup E hE ⟶ integralCurveGroup V hV)
  {H : Scheme.{u}} (i : H ⟶ integralCurve E) (k : H ⟶ Spec (.of R))
  (h : IsPullback i k f.hom.hom.hom.left (integralCurveZero V))

/-- The original group morphism carries the actual zero to zero. -/
@[reassoc] theorem zero_map :
    integralCurveZero E ≫ f.hom.hom.hom.left = integralCurveZero V :=
  congrArg Over.Hom.left (IsMonHom.one_hom f.hom.hom.hom)

/-- The original group morphism commutes with the actual cubic negation. -/
@[reassoc] theorem negation_map :
    integralCurveNegation E ≫ f.hom.hom.hom.left =
      f.hom.hom.hom.left ≫ integralCurveNegation V :=
  congrArg Over.Hom.left (GrpObj.inv_hom f.hom.hom.hom)

/-- Construct the identity on the exact original Cartesian fiber. -/
def zero : Spec (.of R) ⟶ H :=
  h.lift (integralCurveZero E) (𝟙 _) (by rw [zero_map, Category.id_comp])

/-- The constructed fiber identity retains the original zero section. -/
@[reassoc] theorem zero_inclusion : zero E V hE hV f i k h ≫ i = integralCurveZero E :=
  h.lift_fst _ _ _

/-- The fiber identity is a section of its original structure morphism. -/
@[reassoc] theorem zero_structure : zero E V hE hV f i k h ≫ k = 𝟙 _ := h.lift_snd _ _ _

/-- Construct the inverse on the full original identity fiber. -/
def negation : H ⟶ H :=
  h.lift (i ≫ integralCurveNegation E) k (by
    rw [Category.assoc, negation_map, ← Category.assoc, h.w, Category.assoc,
      integralCurveZero_negation])

/-- The fiber inverse retains the original cubic inverse. -/
@[reassoc] theorem negation_inclusion :
    negation E V hE hV f i k h ≫ i = i ≫ integralCurveNegation E := h.lift_fst _ _ _

/-- The fiber inverse remains over the original base. -/
@[reassoc] theorem negation_structure : negation E V hE hV f i k h ≫ k = k :=
  h.lift_snd _ _ _

/-- The constructed inverse is involutive on the full original fiber. -/
@[reassoc] theorem negation_comp :
    negation E V hE hV f i k h ≫ negation E V hE hV f i k h = 𝟙 _ := by
  apply h.hom_ext
  · simp only [Category.assoc, negation_inclusion, negation_inclusion_assoc,
      integralCurveNegation_comp, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, negation_structure, Category.id_comp]

end FLT.Mazur.WeierstrassIdentityFiber
