/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualChartQuotient

/-!
# Descending full same-chart saturated opens

An open preserved by every actual same-chart arrow gives an open of the full
assembled orbit space. Its selected chart preimage is exactly the original open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n] (b : Bool)

/-- Saturation under the full arrow scheme makes the orbit image have the exact preimage. -/
theorem chartProjection_preimage_image_of_saturated (V : (normalizedLocus n b).Opens)
    (hV : productArrowSource n b b ⁻¹ᵁ V = productArrowTarget n b b ⁻¹ᵁ V) :
    chartProjection n b ⁻¹' (chartProjection n b '' (V : Set _)) = V := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha, ht⟩ := (chartProjection_eq_iff n b b y x).mp he
    have h := Set.ext_iff.mp (congrArg SetLike.coe hV) a
    change productArrowSource n b b a ∈ V ↔ productArrowTarget n b b a ∈ V at h
    rw [ha, ht] at h
    exact h.mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The actual orbit image of any full same-chart saturated open is open. -/
theorem chartProjection_image_isOpen_of_saturated (V : (normalizedLocus n b).Opens)
    (hV : productArrowSource n b b ⁻¹ᵁ V = productArrowTarget n b b ⁻¹ᵁ V) :
    IsOpen (chartProjection n b '' (V : Set _)) := by
  apply (chartProjection_isOpen_iff n b _ ?_).mpr
  · rw [chartProjection_preimage_image_of_saturated n b V hV]
    exact V.isOpen
  · rintro _ ⟨x, _, rfl⟩
    exact normalized_mem_integerOpen n b x

/-- A genuine quotient open obtained from a saturated original characteristic chart open. -/
def chartDescendOpen (V : (normalizedLocus n b).Opens)
    (hV : productArrowSource n b b ⁻¹ᵁ V = productArrowTarget n b b ⁻¹ᵁ V) :
    Opens (Orbit n) :=
  ⟨chartProjection n b '' (V : Set _),
    chartProjection_image_isOpen_of_saturated n b V hV⟩

/-- The descended open stays inside its actual characteristic orbit open. -/
theorem chartDescendOpen_le (V : (normalizedLocus n b).Opens)
    (hV : productArrowSource n b b ⁻¹ᵁ V = productArrowTarget n b b ⁻¹ᵁ V) :
    chartDescendOpen n b V hV ≤ integerOpen n (chartInteger b) := by
  rintro _ ⟨x, _, rfl⟩
  exact normalized_mem_integerOpen n b x

/-- Pullback recovers the exact original open, without replacing its arrow relation. -/
theorem chartDescendOpen_preimage (V : (normalizedLocus n b).Opens)
    (hV : productArrowSource n b b ⁻¹ᵁ V = productArrowTarget n b b ⁻¹ᵁ V) :
    (Opens.map (TopCat.ofHom ⟨chartProjection n b, chartProjection_continuous n b⟩)).obj
      (chartDescendOpen n b V hV) = V :=
  Opens.ext (chartProjection_preimage_image_of_saturated n b V hV)

end FLT.Mazur.CyclicCharacteristicOrbit
