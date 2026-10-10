/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientChartPreimage

/-!
# Cartesian affine charts of the global quotient

The proved inverse-image identity gives the universal property of each
chart square. Consequently the global quotient map is integral, since its
base changes to the quotient charts are the original affine quotient maps.
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

/-- Each original invariant affine chart is the pullback of its actual quotient chart. -/
theorem chart_isPullback (U : Chart ρ) :
    IsPullback U.val.ι (quotientMap (action ρ U)) (map ρ hcover) (chartMap ρ U) := by
  refine ⟨⟨ι_map ρ hcover U⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    apply IsOpenImmersion.lift U.val.ι c.fst
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    apply (map_preimage_chart ρ hcover U).le
    refine ⟨c.snd y, ?_⟩
    exact congrArg (fun f ↦ f y) c.condition.symm
  · intro c
    exact IsOpenImmersion.lift_fac _ _ _
  · intro c
    rw [← cancel_mono (chartMap ρ U), Category.assoc,
      ← show U.val.ι ≫ map ρ hcover = quotientMap (action ρ U) ≫ chartMap ρ U from
        ι_map ρ hcover U, IsOpenImmersion.lift_fac_assoc]
    exact c.condition
  · intro c m hm _
    rw [← cancel_mono U.val.ι, IsOpenImmersion.lift_fac]
    exact hm

/-- The constructed global quotient morphism is integral. -/
instance map_integral : IsIntegralHom (map ρ hcover) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsIntegralHom) (gluedCover ρ)
  intro U
  change IsIntegralHom (pullback.snd (map ρ hcover) (chartMap ρ U))
  rw [← (chart_isPullback ρ hcover U).isoPullback_inv_snd]
  infer_instance

/-- The scheme-level global quotient map is surjective. -/
instance map_isSurjective : Surjective (map ρ hcover) := ⟨map_surjective ρ hcover⟩

/-- The topology of the glued scheme is the quotient topology of the original scheme. -/
lemma map_isQuotientMap : Topology.IsQuotientMap (map ρ hcover) :=
  (map ρ hcover).isClosedMap.isQuotientMap
    (map ρ hcover).continuous (map_surjective ρ hcover)

/-- The fibers of the constructed global quotient are exactly the original group orbits. -/
theorem map_eq_iff_orbit (x y : X) :
    map ρ hcover x = map ρ hcover y ↔ ∃ g : G, y = (ρ g).hom x := by
  constructor
  · intro h
    obtain ⟨U, a, rfl⟩ := (sourceCover ρ hcover).exists_eq x
    have hy : y ∈ U.val := by
      rw [← map_preimage_chart ρ hcover U]
      refine ⟨quotientMap (action ρ U) a, ?_⟩
      exact (map_apply_chart ρ hcover U a).symm.trans h
    let b : U.val.toScheme := ⟨y, hy⟩
    have he : quotientMap (action ρ U) a = quotientMap (action ρ U) b := by
      apply (chartMap ρ U).isOpenEmbedding.injective
      exact (map_apply_chart ρ hcover U a).symm.trans
        (h.trans (map_apply_chart ρ hcover U b))
    obtain ⟨g, hg⟩ := (quotientMap_eq_iff_orbit (action ρ U) a b).mp he
    refine ⟨g, ?_⟩
    exact (congrArg (fun z : U.val.toScheme ↦ z.val) hg).trans (action_apply ρ U g a)
  · rintro ⟨g, rfl⟩
    exact (congrArg (fun f : X ⟶ glued ρ ↦ f x) (map_invariant ρ hcover g)).symm

end FLT.Mazur.StableAffineQuotient
