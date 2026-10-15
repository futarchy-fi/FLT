/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericMapIdentity

/-!
# Generic contraction equality detects the original polygon coordinates

Arbitrary schemes over a nonzero-parameter field map into the original
identity open. On that open the original contraction is an open immersion,
so equal contracted coordinates give equal original coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "c" => completePointToIntegralCubic K n h i
local notation "U" => completePointIdentityOpen K n h i

/-- The actual contraction is a monomorphism on the original identity open. -/
theorem completePointIdentityContraction_mono : Mono ((U).ι ≫ (c)) := by
  rw [← completePointSmoothCubicIso_inclusion]
  infer_instance

/-- The generic contraction detects maps without flatness assumptions on the test scheme. -/
theorem completeGeneric_contraction_ext
    (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
    {T : Scheme} (p q : T ⟶ exactVeroneseProj K n h) (b : T ⟶ Spec (.of L))
    (hp : p ≫ (π) = b ≫ Spec.map (CommRingCat.ofHom a))
    (hq : q ≫ (π) = b ≫ Spec.map (CommRingCat.ofHom a))
    (he : p ≫ (c) = q ≫ (c)) : p = q := by
  let _ := completePointIdentityContraction_mono K n h i
  let p' := completeGenericMapToIdentity K n h i L a ha p b hp
  let q' := completeGenericMapToIdentity K n h i L a ha q b hq
  have hp' : p' ≫ (U).ι = p := completeGenericMapToIdentity_inclusion K n h i L a ha p b hp
  have hq' : q' ≫ (U).ι = q := completeGenericMapToIdentity_inclusion K n h i L a ha q b hq
  have he' : p' = q' := (cancel_mono ((U).ι ≫ (c))).mp (by
    simpa only [← Category.assoc, hp', hq'] using he)
  rw [← hp', ← hq', he']

end FLT.Mazur.PolygonInfinitesimalStages
