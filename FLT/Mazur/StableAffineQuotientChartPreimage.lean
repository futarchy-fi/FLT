/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientMap

/-!
# Recovering the original affine charts from the glued quotient

The inverse image of each quotient chart is exactly its original stable
open. This follows from the actual orbit fibers and the point-identification
theorem for the constructed scheme gluing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X) (hcover : ⨆ U : Chart ρ, U.val = ⊤)

/-- The global map on a chart point is its affine quotient followed by its chart inclusion. -/
lemma map_apply_chart (U : Chart ρ) (x : U.val.toScheme) :
    map ρ hcover x.val = chartMap ρ U (quotientMap (action ρ U) x) :=
  congrArg (fun f : U.val.toScheme ⟶ glued ρ ↦ f x) (ι_map ρ hcover U)

/-- Equal points in the gluing preserve membership in the original stable chart. -/
lemma chartMap_eq_mem {U V : Chart ρ} (a : U.val.toScheme) (q : quotient (action ρ V))
    (he : chartMap ρ U (quotientMap (action ρ U) a) = chartMap ρ V q) : a.val ∈ V.val := by
  obtain ⟨T, hU, hV, z, hz, _⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram ρ)).mp he
  obtain ⟨t, rfl⟩ := (quotientMap (action ρ T)).surjective z
  change inclusion ρ (leOfHom hU) (quotientMap (action ρ T) t) =
    quotientMap (action ρ U) a at hz
  rw [inclusion_apply_quotientMap] at hz
  obtain ⟨g, hg⟩ := (quotientMap_eq_iff_orbit (action ρ U) _ _).mp hz
  have ha : a.val = (ρ g).hom t.val := by
    have hh := congrArg (fun x : U.val.toScheme ↦ x.val) hg
    simpa only [action_apply, Scheme.homOfLE_apply] using hh
  have ht : t.val ∈ V.val := leOfHom hV t.property
  rw [ha]
  change t.val ∈ (ρ g).hom ⁻¹ᵁ V.val
  rwa [V.property.2 g]

/-- The inverse image of an actual quotient chart is exactly its original affine open. -/
lemma map_preimage_chart (U : Chart ρ) :
    map ρ hcover ⁻¹ᵁ (chartMap ρ U).opensRange = U.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨V, a, rfl⟩ := (sourceCover ρ hcover).exists_eq x
    obtain ⟨q, hq⟩ := hx
    apply chartMap_eq_mem ρ a q
    exact (map_apply_chart ρ hcover V a).symm.trans hq.symm
  · intro hx
    refine ⟨quotientMap (action ρ U) ⟨x, hx⟩, ?_⟩
    exact (map_apply_chart ρ hcover U ⟨x, hx⟩).symm

end FLT.Mazur.StableAffineQuotient
