/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealFamilies
public import FLT.Mazur.IdealSheafOpenCoverDetection

/-!
# Full relative ideal families are detected on any base open cover

Base changing an arbitrary open cover of the test scheme gives the intrinsic
relative ambient cover. Equality of full families is detected on this cover,
without an affineness assumption on its objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {A S X : Scheme.{u}} (a : A ⟶ S) (s : X ⟶ S) (C : X.OpenCover.{u})

/-- The intrinsic relative ambients over a base open cover cover the full relative ambient. -/
def relativeIdealAmbientCover : (pullback s a).OpenCover where
  I₀ := C.I₀
  X i := pullback (C.f i ≫ s) a
  f i := relativeIdealAmbientMap a s (C.f i ≫ s) (C.f i) rfl
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
    · let D := C.pullback₁ (pullback.fst s a)
      obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq D x
      let h := relativeIdealAmbientMap_isPullback a s (C.f i ≫ s) (C.f i) rfl
      exact ⟨i, h.isoPullback.inv y,
        (congrArg (fun f ↦ f y) h.isoPullback_inv_fst).trans hy⟩
    · exact MorphismProperty.of_isPullback
        (relativeIdealAmbientMap_isPullback a s (C.f i ≫ s) (C.f i) rfl).flip
        (inferInstance : IsOpenImmersion (C.f i))

/-- Full relative families agree if their actual pullbacks to a base cover agree. -/
theorem relativeIdealFamily_ext_openCover (d : ℕ) (J K : RelativeIdealFamilies a d s)
    (h : ∀ i, relativeIdealFamilyBaseChange a d s (C.f i ≫ s) (C.f i) rfl J =
      relativeIdealFamilyBaseChange a d s (C.f i ≫ s) (C.f i) rfl K) : J = K := by
  apply Subtype.ext
  apply BaseAdicThickening.idealSheaf_ext_of_openCover (relativeIdealAmbientCover a s C)
  intro i
  exact congrArg Subtype.val (h i)

end FLT.Mazur.ClosedIdealCover
