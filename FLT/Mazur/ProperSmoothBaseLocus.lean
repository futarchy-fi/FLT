/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The base open where a proper finitely presented family is smooth

Remove the closed image of the nonsmooth locus of the total space. This gives
exactly the largest base open on which the original family is smooth.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme} (f : X ⟶ S) [UniversallyClosed f]
  [LocallyOfFinitePresentation f]

/-- The original base with the image of all nonsmooth total-space points removed. -/
def properSmoothBaseLocus : S.Opens :=
  ⟨(f '' (f.smoothLocus : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩

/-- Membership means every point over the original base point is relatively smooth. -/
theorem mem_properSmoothBaseLocus (s : S) :
    s ∈ properSmoothBaseLocus f ↔ ∀ x : X, f x = s → x ∈ f.smoothLocus := by
  change s ∉ f '' (f.smoothLocus : Set X)ᶜ ↔ _
  simp only [Set.mem_image, Set.mem_compl_iff, not_exists, not_and]
  constructor
  · intro h x hx
    by_contra hn
    exact h x hn hx
  · intro h x hn hx
    exact hn (h x hx)

/-- An open lies in the smooth base locus exactly when its whole preimage is smooth. -/
theorem le_properSmoothBaseLocus_iff (U : S.Opens) :
    U ≤ properSmoothBaseLocus f ↔ f ⁻¹ᵁ U ≤ f.smoothLocus := by
  constructor
  · intro h x hx
    exact (mem_properSmoothBaseLocus f (f x)).mp (h hx) x rfl
  · intro h s hs
    exact (mem_properSmoothBaseLocus f s).mpr fun x hx ↦ h (by change f x ∈ U; rwa [hx])

/-- The original family restricted to an open is smooth exactly on this base locus. -/
theorem smooth_restrict_iff_le_properSmoothBaseLocus (U : S.Opens) :
    Smooth (f ∣_ U) ↔ U ≤ properSmoothBaseLocus f := by
  rw [le_properSmoothBaseLocus_iff]
  have h : Smooth ((f ⁻¹ᵁ U).ι ≫ f) ↔ f ⁻¹ᵁ U ≤ f.smoothLocus := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    constructor
    · intro he x hx
      have hm : (⟨x, hx⟩ : (f ⁻¹ᵁ U).toScheme) ∈
          (f ⁻¹ᵁ U).ι ⁻¹ᵁ f.smoothLocus := by rw [he]; trivial
      exact hm
    · intro he
      apply top_unique
      intro x _
      exact he x.property
  rw [← h, ← morphismRestrict_ι]
  constructor
  · intro hf
    let _ := hf
    infer_instance
  · exact MorphismProperty.of_postcomp @Smooth (W' := @IsOpenImmersion)
      (f ∣_ U) U.ι inferInstance

/-- The original restriction to the constructed base open is smooth. -/
instance properSmoothBaseLocus_smooth : Smooth (f ∣_ properSmoothBaseLocus f) :=
  (smooth_restrict_iff_le_properSmoothBaseLocus f _).mpr le_rfl

end FLT.Mazur.FCurve
