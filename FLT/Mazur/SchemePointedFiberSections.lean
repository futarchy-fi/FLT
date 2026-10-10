/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeProperGeometricFiberSections
public import FLT.Mazur.ProperIntegralConstantSections

/-!
# H0 comparison on every field base change of a pointed family

A section supplies a rational point on every field base change. For a
proper geometrically integral family this identifies its
fiber global functions with that field, without algebraic closedness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeProperGeometricFiberSections
variable {X S T : Scheme} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

/-- The actual section obtained on a fiber product by base change. -/
def baseChangedSection (a : T ⟶ S) : T ⟶ Limits.pullback f a :=
  Limits.pullback.lift (a ≫ s) (𝟙 T)
    (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

/-- The base-changed section is a section of the original fiber-product projection. -/
lemma baseChangedSection_projection (a : T ⟶ S) :
    baseChangedSection f s hs a ≫ Limits.pullback.snd f a = 𝟙 T :=
  Limits.pullback.lift_snd _ _ _

variable [IsProper f] [GeometricallyIntegral f]
variable {K : Type} [Field K]
include s hs

/-- Every field base change has constant global functions by the existing pointed theorem. -/
lemma pointedFiber_constantSections (a : Spec (.of K) ⟶ S) :
    FCurve.HasConstantGlobalSections (Limits.pullback.snd f a) := by
  let _ := GeometricallyIntegral.isIntegral_of_subsingleton (Limits.pullback.snd f a)
  exact FCurve.constantGlobalSections_of_proper_integral_section
    (Limits.pullback.snd f a) (baseChangedSection f s hs a)
    (baseChangedSection_projection f s hs a)

/-- Every field base change has the actual constants-to-cohomology linear equivalence. -/
def pointedFiberH0Equiv (a : Spec (.of K) ⟶ S) :
    K ≃ₗ[K] FCurve.H0 (Limits.pullback.snd f a) :=
  FCurve.scalarH0ConstantsEquiv _ (pointedFiber_constantSections f s hs a)

/-- The equivalence is the existing inclusion of constants into actual H0. -/
lemma pointedFiberH0Equiv_apply (a : Spec (.of K) ⟶ S) (r : K) :
    pointedFiberH0Equiv f s hs a r =
      FCurve.scalarH0Constants (Limits.pullback.snd f a) r := rfl

/-- Degree-zero cohomology of every field base change has dimension one. -/
lemma pointedFiber_finrank_H0 (a : Spec (.of K) ⟶ S) :
    Module.finrank K (FCurve.H0 (Limits.pullback.snd f a)) = 1 :=
  FCurve.finrank_H0_of_constantGlobalSections _ (pointedFiber_constantSections f s hs a)

end FLT.Mazur.SchemeProperGeometricFiberSections
