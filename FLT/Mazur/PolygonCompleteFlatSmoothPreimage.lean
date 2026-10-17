/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericMapIdentity

/-!
# Smooth-input detection on arbitrary flat original test schemes

Equality over the smooth preimage determines maps into any separated target.
The proof uses the existing generic identity-preimage detection theorem and
retains all nilpotents in the original test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "π" => exactVeroneseProjToBase K n h

/-- The original identity preimage is contained in the actual full smooth preimage. -/
theorem completeIdentityPreimage_le_smooth {T : Scheme}
    (p : T ⟶ exactVeroneseProj K n h) :
    p ⁻¹ᵁ completePointIdentityOpen K n h 0 ≤ p ⁻¹ᵁ (π).smoothLocus := by
  intro x hx
  exact completePointIdentityOpen_le_smooth K n h 0 hx

/-- Smooth-preimage equality detects maps on every flat original-base test scheme. -/
theorem completeFlat_smoothPreimage_ext {T Y : Scheme}
    (p : T ⟶ exactVeroneseProj K n h) [Flat (p ≫ (π))]
    (v : Y ⟶ Spec (.of (PowerSeries K))) [IsSeparated v]
    (f g : T ⟶ Y) (hb : f ≫ v = g ≫ v)
    (he : (p ⁻¹ᵁ (π).smoothLocus).ι ≫ f = (p ⁻¹ᵁ (π).smoothLocus).ι ≫ g) :
    f = g := by
  apply completeFlat_identityPreimage_ext K n h 0 p v f g hb
  have hl := Scheme.homOfLE_ι T (completeIdentityPreimage_le_smooth K n h p)
  rw [← hl, Category.assoc, he, Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages
