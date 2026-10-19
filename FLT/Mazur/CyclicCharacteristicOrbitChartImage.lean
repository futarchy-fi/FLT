/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitIntegerOpens

/-!
# Exact images of the normalized characteristic charts in the full orbit space

The actual transition covers give a representative in the selected chart for
every orbit on which its auxiliary integer is invertible. Consequently each
chart image is exactly that open, with all full-relation arrows still retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The full orbit projection from one original normalized characteristic chart. -/
def chartProjection (b : Bool) : normalizedLocus n b → Orbit n :=
  projection n ∘ normalizedDisjointInclusion n b

/-- The chart orbit map is continuous. -/
theorem chartProjection_continuous (b : Bool) : Continuous (chartProjection n b) :=
  (projection_continuous n).comp (normalizedDisjointInclusion n b).continuous

/-- The two parameters of every actual transition point have the same full orbit. -/
theorem chartProjection_transition (b : Bool) (i : (transitionCover n b).I₀)
    (x : (transitionCover n b).X i) :
    chartProjection n (!b) (transitionTarget n b i x) =
      chartProjection n b (transitionSource n b i x) := by
  simpa only [finiteProjection_apply, chartProjection, Function.comp_apply] using
    finiteProjection_transition n b i x

/-- The selected chart represents every orbit on its integer-invertible open. -/
theorem chartProjection_range (b : Bool) :
    Set.range (chartProjection n b) = (integerOpen n (chartInteger b)).carrier := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact normalized_mem_integerOpen n b x
  · intro hz
    obtain ⟨x, rfl⟩ := projection_surjective n z
    obtain ⟨c, y, rfl⟩ := normalizedDisjointSource_covers n x
    by_cases hc : c = b
    · subst c
      exact ⟨y, rfl⟩
    · have hb : b = !c := by cases b <;> cases c <;> simp_all
      subst b
      have hy : y ∈ transitionOpen n c :=
        (mem_integerOpen_iff n (chartInteger (!c)) c y).mp hz
      obtain ⟨i, t, ht⟩ := (transitionSource_covers n c y).mpr hy
      refine ⟨transitionTarget n c i t, ?_⟩
      rw [chartProjection_transition, ht]
      rfl

/-- The full orbit image of each finite relabeling quotient is the same exact open. -/
theorem finiteProjection_range (b : Bool) :
    Set.range (finiteProjection n b) = (integerOpen n (chartInteger b)).carrier := by
  rw [← chartProjection_range]
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (normalizedQuotientMap n b).surjective y
    exact ⟨x, finiteProjection_apply n b x |>.symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨normalizedQuotientMap n b x, finiteProjection_apply n b x⟩

/-- The normalized chart gives an actual surjection onto its characteristic orbit open. -/
def chartToIntegerOpen (b : Bool) :
    (normalizedLocus n b).toTopCat ⟶ (Opens.toTopCat (space n)).obj
      (integerOpen n (chartInteger b)) :=
  TopCat.ofHom ⟨fun x => ⟨chartProjection n b x, normalized_mem_integerOpen n b x⟩,
    (chartProjection_continuous n b).subtype_mk _⟩

/-- Surjectivity uses the constructed cross-characteristic comparison covers. -/
theorem chartToIntegerOpen_surjective (b : Bool) :
    Function.Surjective (chartToIntegerOpen n b) := by
  intro z
  obtain ⟨x, hx⟩ := (Set.ext_iff.mp (chartProjection_range n b) z.val).mpr z.property
  exact ⟨x, Subtype.ext hx⟩

end FLT.Mazur.CyclicCharacteristicOrbit
