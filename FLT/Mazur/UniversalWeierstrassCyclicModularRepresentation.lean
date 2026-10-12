/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicModularClasses

/-!
# Representation of the original full marked chart-family presheaf

The actual full closed slice represents genuine isomorphism classes of original
smooth Weierstrass chart families, naturally on all source schemes. No claim
that all generalized elliptic curves admit these chart presentations is made.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
variable (n : ℕ) [NeZero n]

/-- Identity source change fixes the original full marked family class. -/
theorem cyclicMarkedFamilyClassesPullback_id (T : Scheme) :
    cyclicMarkedFamilyClassesPullback n (𝟙 T) = id := by
  funext q
  induction q using Quotient.inductionOn with
  | h f =>
    change Quotient.mk _ (𝟙 T ≫ f) = Quotient.mk _ f
    rw [Category.id_comp]

/-- Successive source changes agree with source change along the composite. -/
theorem cyclicMarkedFamilyClassesPullback_comp {T U V : Scheme} (k : U ⟶ T) (j : V ⟶ U) :
    cyclicMarkedFamilyClassesPullback n (j ≫ k) =
      cyclicMarkedFamilyClassesPullback n j ∘ cyclicMarkedFamilyClassesPullback n k := by
  funext q
  induction q using Quotient.inductionOn with
  | h f =>
    change Quotient.mk _ ((j ≫ k) ≫ f) = Quotient.mk _ (j ≫ k ≫ f)
    rw [Category.assoc]

/-- The presheaf of genuine original full marked smooth chart-family classes. -/
def cyclicMarkedFamilyClassPresheaf : Schemeᵒᵖ ⥤ Type _ where
  obj T := CyclicMarkedFamilyClasses n T.unop
  map k := ↾(cyclicMarkedFamilyClassesPullback n k.unop)
  map_id T := by
    ext q
    exact congrFun (cyclicMarkedFamilyClassesPullback_id n T.unop) q
  map_comp k j := by
    ext q
    exact congrFun (cyclicMarkedFamilyClassesPullback_comp n k.unop j.unop) q

/-- The original full closed slice represents the actual marked chart-family quotient presheaf. -/
def cyclicMarkedFamilyClassRepresentation :
    cyclicMarkedFamilyClassPresheaf n ≅ yoneda.obj (cyclicNormalizedSlice n) :=
  NatIso.ofComponents (fun T ↦ (cyclicMarkedFamilyClassesEquiv n T.unop).toIso)
    (by
      intro T U k
      apply ConcreteCategory.hom_ext
      intro q
      exact cyclicMarkedFamilyClassesEquiv_natural n k.unop q)

/-- The representing map is exactly the original full slice normalization. -/
theorem cyclicMarkedFamilyClassRepresentation_mk {T : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    (cyclicMarkedFamilyClassRepresentation n).hom.app (Opposite.op T) (Quotient.mk _ f) =
      f ≫ cyclicNormalizationSliceMap n := rfl

end FLT.Mazur.UniversalWeierstrass
