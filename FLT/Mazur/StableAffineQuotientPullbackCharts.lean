/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientBaseCharts
public import FLT.Mazur.FiniteGroupPullbackComparison

/-!
# Cartesian affine source charts after quotient base change

The affine pullbacks over subordinate base charts embed as actual open
subschemes of the global pullback. Their actions agree with the global
pullback action, and these source charts cover the entire pullback.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X S : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X) (hcover : ⨆ U : Chart ρ, U.val = ⊤) (f : S ⟶ glued ρ)

/-- The local affine source maps to the actual global pullback. -/
def sourceChartMap (c : BaseChart ρ f) :
    baseChartSource ρ f c ⟶ pullback (map ρ hcover) f :=
  pullback.lift (pullback.fst _ _ ≫ c.val.1.val.ι)
    (pullback.snd _ _ ≫ c.val.2.val.ι) (by
      rw [Category.assoc, ι_map]
      change pullback.fst _ _ ≫ (quotientMap (action ρ c.val.1) ≫ chartMap ρ c.val.1) = _
      rw [← Category.assoc, pullback.condition, Category.assoc, baseChartMap_fac,
        Category.assoc])

/-- The local source chart preserves the original-scheme projection. -/
@[reassoc]
lemma sourceChartMap_fst (c : BaseChart ρ f) :
    sourceChartMap ρ hcover f c ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ c.val.1.val.ι := pullback.lift_fst _ _ _

/-- The local source chart preserves the new-base projection. -/
@[reassoc]
lemma sourceChartMap_snd (c : BaseChart ρ f) :
    sourceChartMap ρ hcover f c ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ c.val.2.val.ι := pullback.lift_snd _ _ _

/-- The local source is exactly the inverse image of its affine base chart. -/
theorem sourceChart_isPullback (c : BaseChart ρ f) :
    IsPullback (sourceChartMap ρ hcover f c) (pullback.snd _ _)
      (pullback.snd (map ρ hcover) f) c.val.2.val.ι := by
  have h := (IsPullback.of_hasPullback (quotientMap (action ρ c.val.1))
    (baseChartMap ρ f c)).paste_horiz (chart_isPullback ρ hcover c.val.1)
  rw [baseChartMap_fac, ← sourceChartMap_fst ρ hcover f c] at h
  exact h.of_right (sourceChartMap_snd ρ hcover f c) (IsPullback.of_hasPullback _ _)

/-- Each local source is an actual open subscheme of the global pullback. -/
instance sourceChartMap_isOpenImmersion (c : BaseChart ρ f) :
    IsOpenImmersion (sourceChartMap ρ hcover f c) := by
  rw [← (sourceChart_isPullback ρ hcover f c).isoPullback_hom_fst]
  infer_instance

/-- The actual local group action on an affine source chart. -/
def sourceChartAction (c : BaseChart ρ f) : G →* Aut (baseChartSource ρ f c) :=
  FiniteGroupPullback.action (action ρ c.val.1) _
    (quotientMap_invariant (action ρ c.val.1)) (baseChartMap ρ f c)

/-- The source chart inclusion is equivariant for the actual pullback actions. -/
@[reassoc]
lemma sourceChartMap_equivariant (c : BaseChart ρ f) (g : G) :
    (sourceChartAction ρ f c g).hom ≫ sourceChartMap ρ hcover f c =
      sourceChartMap ρ hcover f c ≫
        (FiniteGroupPullback.action ρ _ (map_invariant ρ hcover) f g).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, sourceChartMap_fst, FiniteGroupPullback.action_fst,
      sourceChartMap_fst_assoc]
    have h := FiniteGroupPullback.action_fst (action ρ c.val.1) _
      (quotientMap_invariant (action ρ c.val.1)) (baseChartMap ρ f c) g
    have ht := congrArg (fun k ↦ k ≫ c.val.1.val.ι) h
    simp only [Category.assoc, action,
      FiniteGroupRestriction.restrictedAction_hom_ι] at ht
    exact ht
  · simp only [Category.assoc, sourceChartMap_snd, FiniteGroupPullback.action_snd]
    exact FiniteGroupPullback.action_snd_assoc _ _ _ _ _ _

/-- Every point of the global pullback lies in one of these actual affine source charts. -/
theorem exists_sourceChart (x : (pullback (map ρ hcover) f : Scheme.{u})) :
    ∃ (c : BaseChart ρ f) (y : baseChartSource ρ f c), sourceChartMap ρ hcover f c y = x := by
  obtain ⟨c, hc⟩ := exists_baseChart ρ f (pullback.snd (map ρ hcover) f x)
  have hx : x ∈ Set.range (pullback.fst (pullback.snd (map ρ hcover) f) c.val.2.val.ι) := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact ⟨⟨pullback.snd (map ρ hcover) f x, hc⟩, rfl⟩
  obtain ⟨z, hz⟩ := hx
  refine ⟨c, (sourceChart_isPullback ρ hcover f c).isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hz

/-- The actual affine source charts form a scheme open cover of the global pullback. -/
def pullbackSourceCover : (pullback (map ρ hcover) f).OpenCover where
  I₀ := BaseChart ρ f
  X c := baseChartSource ρ f c
  f c := sourceChartMap ρ hcover f c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨exists_sourceChart ρ hcover f, inferInstance⟩

end FLT.Mazur.StableAffineQuotient
