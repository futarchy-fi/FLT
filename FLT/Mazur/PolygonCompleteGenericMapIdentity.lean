/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityCubicGroup
public import FLT.Mazur.PolygonCompleteGenericMorphismExt

/-!
# Arbitrary generic test schemes factor through the original identity open

The factorization is constructed by the original Cartesian field fiber.
Consequently equality on the identity preimage detects maps from flat sources.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "U" => completePointIdentityOpen K n h i
variable (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
local notation "s" => Spec.map (CommRingCat.ofHom a)
variable {T : Scheme} (p : T ⟶ exactVeroneseProj K n h) (q : T ⟶ Spec (.of L))
  (hp : p ≫ exactVeroneseProjToBase K n h =
    q ≫ Spec.map (CommRingCat.ofHom a))

/-- Every map over a nonzero-parameter field has a constructed original identity coordinate. -/
def completeGenericMapToIdentity : T ⟶ (U).toScheme :=
  (pullback.lift p q hp : T ⟶ pullback (π) (s)) ≫
    completePointFieldToIdentity K n h i L a ha
      (pullback.fst (π) (s)) (pullback.snd (π) (s)) (IsPullback.of_hasPullback (π) (s))

/-- The generic coordinate retains the actual original whole-family morphism. -/
@[reassoc] theorem completeGenericMapToIdentity_inclusion :
    completeGenericMapToIdentity K n h i L a ha p q hp ≫ (U).ι = p := by
  rw [completeGenericMapToIdentity, Category.assoc,
    completePointFieldToIdentity_inclusion, pullback.lift_fst]

include ha hp in
/-- Every generic test scheme lands in the full original identity open. -/
theorem completeGenericMap_preimage_identity : p ⁻¹ᵁ (U) = ⊤ := by
  apply top_unique
  intro x _
  have he := completeGenericMapToIdentity_inclusion K n h i L a ha p q hp
  rw [← he]
  exact (completeGenericMapToIdentity K n h i L a ha p q hp x).2

omit L a ha in
/-- Equality on the identity preimage determines maps from any flat original-base source. -/
theorem completeFlat_identityPreimage_ext {X Y : Scheme}
    (p : X ⟶ exactVeroneseProj K n h) [Flat (p ≫ (π))]
    (v : Y ⟶ Spec (.of (PowerSeries K))) [IsSeparated v]
    (f g : X ⟶ Y) (hb : f ≫ v = g ≫ v)
    (he : (p ⁻¹ᵁ (U)).ι ≫ f = (p ⁻¹ᵁ (U)).ι ≫ g) : f = g := by
  let L := FractionRing (PowerSeries K)
  let a := algebraMap (PowerSeries K) L
  have ha : a PowerSeries.X ≠ 0 := by
    intro hz
    exact PowerSeries.X_ne_zero ((IsFractionRing.injective (PowerSeries K) L)
      (hz.trans (map_zero a).symm))
  let b := Spec.map (CommRingCat.ofHom a)
  let r := pullback.fst (p ≫ (π)) b
  let q := pullback.snd (p ≫ (π)) b
  have hr : (r ≫ p) ⁻¹ᵁ (U) = ⊤ :=
    completeGenericMap_preimage_identity K n h i L a ha (r ≫ p) q
      (by simpa only [Category.assoc] using pullback.condition (f := p ≫ (π)) (g := b))
  let l : pullback (p ≫ (π)) b ⟶ (p ⁻¹ᵁ (U)).toScheme :=
    IsOpenImmersion.lift (p ⁻¹ᵁ (U)).ι r (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hr.ge (show x ∈ ⊤ from trivial))
  have hl : l ≫ (p ⁻¹ᵁ (U)).ι = r := IsOpenImmersion.lift_fac _ _ _
  apply completeFlat_generic_ext K L (p ≫ (π)) v f g hb
  change r ≫ f = r ≫ g
  rw [← hl, Category.assoc, he, Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages
