/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnion

/-!
# Pulling back a covering union of open images

An image inclusion supplies a cover of the entire source by actual
pullbacks. Equality of morphisms can then be tested on these pullbacks.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v

variable {X S : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}}
  (f : S ⟶ X) (g : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (g i)]
  (hc : Set.range f ⊆ (openImageUnion g : Set X))

/-- A covering image union gives an actual pullback cover of the entire source. -/
def openImagePullbackCover : S.OpenCover where
  I₀ := ι
  X i := pullback f (g i)
  f i := pullback.fst f (g i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro s
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hc ⟨s, rfl⟩)
    refine ⟨i, ?_⟩
    change s ∈ (pullback.fst f (g i)).opensRange
    rw [Scheme.Hom.opensRange_pullbackFst]
    exact hi

include hc in
/-- Equality on every literal pullback detects equality on the full source. -/
theorem openImagePullback_hom_ext {T : Scheme.{u}} (a b : S ⟶ T)
    (h : ∀ i, pullback.fst f (g i) ≫ a = pullback.fst f (g i) ≫ b) : a = b :=
  (openImagePullbackCover f g hc).hom_ext a b h

end FLT.Mazur
