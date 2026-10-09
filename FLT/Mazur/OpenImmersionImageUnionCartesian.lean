/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnionGluing

/-!
# Cartesian maps between ambient image unions

Exact inverse images of the constituent open images construct a cartesian
map on their whole unions. Local commuting squares determine its restriction
to every original overlap scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v

variable {X Y : Scheme.{u}} {ι : Type v} {V W : ι → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) (g : ∀ i, W i ⟶ Y)
  [∀ i, IsOpenImmersion (f i)] [∀ i, IsOpenImmersion (g i)]
  (t : Y ⟶ X) (ht : ∀ i, t ⁻¹ᵁ (f i).opensRange = (g i).opensRange)

include ht in
/-- Exact constituent inverse images give the exact inverse image of the entire union. -/
theorem openImageUnion_preimage : t ⁻¹ᵁ openImageUnion f = openImageUnion g := by
  simp only [openImageUnion, Scheme.Hom.preimage_iSup, ht]

/-- The actual ambient map lifts to a map of the full image unions. -/
def openImageUnionCartesianMap : (openImageUnion g).toScheme ⟶ (openImageUnion f).toScheme :=
  IsOpenImmersion.lift (openImageUnion f).ι ((openImageUnion g).ι ≫ t) (by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]
    change (openImageUnion g).ι z ∈ t ⁻¹ᵁ openImageUnion f
    rw [openImageUnion_preimage f g t ht]
    exact z.2)

/-- The map of whole unions retains the original ambient map. -/
@[reassoc (attr := simp)] theorem openImageUnionCartesianMap_fac :
    openImageUnionCartesianMap f g t ht ≫ (openImageUnion f).ι = (openImageUnion g).ι ≫ t :=
  IsOpenImmersion.lift_fac _ _ _

/-- The whole union square is cartesian, not just its constituent overlap squares. -/
theorem openImageUnionCartesianMap_isPullback :
    IsPullback (openImageUnionCartesianMap f g t ht) (openImageUnion g).ι
      (openImageUnion f).ι t := by
  apply IsOpenImmersion.isPullback
  · exact (openImageUnionCartesianMap_fac f g t ht).symm
  · simpa only [Scheme.Opens.opensRange_ι] using openImageUnion_preimage f g t ht

/-- Each original commuting overlap square is retained on the entire union. -/
@[reassoc] theorem openImageUnionCartesianMap_component (i : ι)
    (v : W i ⟶ V i) (hv : v ≫ f i = g i ≫ t) :
    openImageUnionMap g i ≫ openImageUnionCartesianMap f g t ht =
      v ≫ openImageUnionMap f i := by
  apply (cancel_mono (openImageUnion f).ι).mp
  rw [Category.assoc, Category.assoc, openImageUnionCartesianMap_fac,
    openImageUnionMap_fac_assoc, openImageUnionMap_fac, hv]

end FLT.Mazur
