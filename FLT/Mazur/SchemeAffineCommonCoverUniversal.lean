/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonBaseCover

/-!
# The universal property of the common affine covering ring

Every pair of covering-ring maps over the chosen common base factors through
the constructed common cover. The factorization retains each map separately.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {A B : CommRingCat.{u}} (f : C.baseRing ⟶ A) (g : C'.baseRing ⟶ A)
variable (ψ : A ⟶ B) (l : C.coverRing ⟶ B) (r : C'.coverRing ⟶ B)
variable (hl : C.ringMap ≫ l = f ≫ ψ) (hr : C'.ringMap ≫ r = g ≫ ψ)

/-- Any common covering ring receives the canonical ring of the common cover. -/
def commonCoverLift : C.commonCoverRing C' f g ⟶ B :=
  pushout.desc (pushout.desc ψ l hl.symm) (pushout.desc ψ r hr.symm)
    (by simp only [baseChange, pushout.inl_desc])

/-- The universal lift lies over the specified map from the common base. -/
@[reassoc (attr := simp)]
theorem commonCoverMap_lift :
    C.commonCoverMap C' f g ≫ C.commonCoverLift C' f g ψ l r hl hr = ψ := by
  simp only [commonCoverMap, commonCoverLift, baseChange, Category.assoc, pushout.inl_desc]

/-- The first original covering-ring map is retained by the universal lift. -/
@[reassoc (attr := simp)]
theorem commonCoverLeft_lift :
    C.commonCoverLeft C' f g ≫ C.commonCoverLift C' f g ψ l r hl hr = l := by
  simp only [commonCoverLeft, commonCoverLift, baseChangeRefinement, baseChange,
    Category.assoc, pushout.inl_desc, pushout.inr_desc]

/-- The second original covering-ring map is retained independently. -/
@[reassoc (attr := simp)]
theorem commonCoverRight_lift :
    C.commonCoverRight C' f g ≫ C.commonCoverLift C' f g ψ l r hl hr = r := by
  simp only [commonCoverRight, commonCoverLift, baseChangeRefinement, baseChange,
    Category.assoc, pushout.inr_desc]

/-- The three structural maps determine a map out of the constructed common cover. -/
theorem commonCoverLift_unique (k : C.commonCoverRing C' f g ⟶ B)
    (hk : C.commonCoverMap C' f g ≫ k = ψ)
    (hkL : C.commonCoverLeft C' f g ≫ k = l)
    (hkR : C.commonCoverRight C' f g ≫ k = r) :
    k = C.commonCoverLift C' f g ψ l r hl hr := by
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · simpa only [commonCoverMap, commonCoverLift, baseChange, Category.assoc,
        pushout.inl_desc] using hk
    · simpa only [commonCoverLeft, commonCoverLift, baseChangeRefinement, baseChange,
        Category.assoc, pushout.inl_desc, pushout.inr_desc] using hkL
  · apply pushout.hom_ext
    · simpa only [commonCoverMap, commonCoverLift, baseChange, Category.assoc,
        pushout.inl_desc, ← pushout.condition_assoc] using hk
    · simpa only [commonCoverRight, commonCoverLift, baseChangeRefinement, baseChange,
        Category.assoc, pushout.inr_desc] using hkR

end FLT.Mazur.SchemeAffineDescent.Chart
