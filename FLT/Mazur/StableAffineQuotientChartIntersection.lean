/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientChartPreimage
public import FLT.Mazur.SchemeFiniteGroupQuotientEpi

/-!
# Scheme intersections of quotient charts

The quotient of the actual stable affine intersection is isomorphic to the
scheme pullback of the two quotient charts. Epimorphism cancellation then
checks descent compatibility on structure sheaves as well as points.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X) (U V : Chart ρ)

/-- The image of the quotient intersection is exactly the intersection of chart images. -/
lemma chartMap_intersection_range :
    Set.range (chartMap ρ (intersection ρ U V)) =
      Set.range (chartMap ρ U) ∩ Set.range (chartMap ρ V) := by
  ext z
  constructor
  · rintro ⟨z, rfl⟩
    constructor
    · exact ⟨inclusion ρ (intersection_le_left ρ U V) z,
        congrArg (fun k ↦ k z) (inclusion_chartMap ρ _)⟩
    · exact ⟨inclusion ρ (intersection_le_right ρ U V) z,
        congrArg (fun k ↦ k z) (inclusion_chartMap ρ _)⟩
  · rintro ⟨⟨a, rfl⟩, b, hb⟩
    obtain ⟨x, rfl⟩ := (quotientMap (action ρ U)).surjective a
    have hx := chartMap_eq_mem ρ x b hb.symm
    let t : (intersection ρ U V).val.toScheme := ⟨x.val, x.property, hx⟩
    refine ⟨quotientMap (action ρ (intersection ρ U V)) t, ?_⟩
    rw [← inclusion_chartMap ρ (intersection_le_left ρ U V), Scheme.Hom.comp_apply,
      inclusion_apply_quotientMap]
    congr 2
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _

/-- The actual intersection quotient is the actual scheme overlap of the quotient charts. -/
def chartIntersectionIso : quotient (action ρ (intersection ρ U V)) ≅
    pullback (chartMap ρ U) (chartMap ρ V) :=
  IsOpenImmersion.isoOfRangeEq (chartMap ρ (intersection ρ U V))
    (pullback.fst (chartMap ρ U) (chartMap ρ V) ≫ chartMap ρ U) (by
      rw [IsOpenImmersion.range_pullback_to_base_of_left, chartMap_intersection_range])

/-- The first overlap projection is the quotient of the first original inclusion. -/
@[reassoc]
lemma chartIntersectionIso_hom_fst :
    (chartIntersectionIso ρ U V).hom ≫ pullback.fst (chartMap ρ U) (chartMap ρ V) =
      inclusion ρ (intersection_le_left ρ U V) := by
  rw [← cancel_mono (chartMap ρ U), Category.assoc, inclusion_chartMap]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The second overlap projection is the quotient of the second original inclusion. -/
@[reassoc]
lemma chartIntersectionIso_hom_snd :
    (chartIntersectionIso ρ U V).hom ≫ pullback.snd (chartMap ρ U) (chartMap ρ V) =
      inclusion ρ (intersection_le_right ρ U V) := by
  rw [← cancel_mono (chartMap ρ V), Category.assoc, ← pullback.condition,
    ← Category.assoc, chartIntersectionIso_hom_fst, inclusion_chartMap, inclusion_chartMap]

/-- Local factorizations of one original map agree on the scheme overlap. -/
lemma localDesc_compatible {Y : Scheme.{u}} (f : X ⟶ Y)
    (a : quotient (action ρ U) ⟶ Y) (b : quotient (action ρ V) ⟶ Y)
    (ha : quotientMap (action ρ U) ≫ a = U.val.ι ≫ f)
    (hb : quotientMap (action ρ V) ≫ b = V.val.ι ≫ f) :
    pullback.fst (chartMap ρ U) (chartMap ρ V) ≫ a =
      pullback.snd (chartMap ρ U) (chartMap ρ V) ≫ b := by
  rw [← cancel_epi (chartIntersectionIso ρ U V).hom,
    chartIntersectionIso_hom_fst_assoc, chartIntersectionIso_hom_snd_assoc]
  apply quotientMap_cancel (action ρ (intersection ρ U V))
  rw [quotient_inclusion_assoc, quotient_inclusion_assoc, ha, hb,
    Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]

end FLT.Mazur.StableAffineQuotient
