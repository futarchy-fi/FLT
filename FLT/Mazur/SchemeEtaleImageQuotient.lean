/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The actual open quotient of an etale full relation kernel

An etale map factors through its actual image as a surjective etale map.
Its original full kernel then descends arbitrary scheme morphisms uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeEtaleImageQuotient
set_option backward.isDefEq.respectTransparency false
variable {A T : Scheme} (w : A ⟶ T) [Etale w]

/-- The image retains the original target scheme structure. -/
def image : T.Opens := ⟨Set.range w, w.isOpenMap.isOpen_range⟩

/-- The complete source projects onto its actual coefficient image. -/
def projection : A ⟶ (image w).toScheme :=
  IsOpenImmersion.lift (image w).ι w (by simp [image])

@[reassoc]
theorem projection_ι : projection w ≫ (image w).ι = w := IsOpenImmersion.lift_fac _ _ _

instance projection_etale : Etale (projection w) := by
  let _ : Etale (projection w ≫ (image w).ι) := by rw [projection_ι]; infer_instance
  exact Etale.of_comp (projection w) (image w).ι

instance projection_surjective : Surjective (projection w) := ⟨by
  rintro ⟨y, x, hx⟩
  refine ⟨x, ?_⟩
  apply (image w).ι.injective
  exact (congrArg (fun g ↦ g x) (projection_ι w)).trans hx⟩

variable {E : Scheme} {p q : E ⟶ A} (H : IsPullback p q w w)

include H in
/-- Factoring through the open image retains both endpoints of the entire kernel. -/
theorem isPullback : IsPullback p q (projection w) (projection w) := by
  apply IsKernelPair.cancel_right (f₂ := (image w).ι)
  · apply (cancel_mono (image w).ι).mp
    simpa only [Category.assoc, projection_ι] using H.w
  · simpa only [projection_ι] using H

variable {J : Scheme} (j : A ⟶ J) (hj : p ≫ j = q ≫ j)

/-- The full original kernel constructs a genuine scheme morphism from the image. -/
def descend : (image w).toScheme ⟶ J :=
  (isColimitCoforkOfEffectiveEpi (projection w) (isPullback w H).cone
    (isPullback w H).isLimit).desc (Cofork.ofπ j hj)

@[reassoc]
theorem projection_descend : projection w ≫ descend w H j hj = j :=
  Cofork.IsColimit.π_desc (isColimitCoforkOfEffectiveEpi (projection w)
    (isPullback w H).cone (isPullback w H).isLimit)

/-- Scheme descent is unique, not only its effect on geometric points. -/
theorem descend_unique (s : (image w).toScheme ⟶ J) (hs : projection w ≫ s = j) :
    s = descend w H j hj := (cancel_epi (projection w)).mp
      (hs.trans (projection_descend w H j hj).symm)

/-- The original coefficient comparison is preserved by descent. -/
@[reassoc]
theorem descend_comp (r : J ⟶ T) (hr : j ≫ r = w) :
    descend w H j hj ≫ r = (image w).ι := by
  apply (cancel_epi (projection w)).mp
  rw [projection_descend_assoc, hr, projection_ι]

end FLT.Mazur.SchemeEtaleImageQuotient
