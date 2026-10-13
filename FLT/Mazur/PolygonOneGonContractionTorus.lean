/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContraction
public import FLT.Mazur.PolygonNormalizationTorusPullback

/-!
# The contraction is an isomorphism over the retained Laurent open

The complete inverse image of the target torus is exactly the retained
original Laurent component. In particular, the square with identity on the
torus is cartesian as schemes, not just on geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

omit [NeZero n] in
/-- Contraction is the identity in the original Laurent coordinates. -/
@[reassoc] theorem torus_contraction :
    (torusToComponent K ≫ componentι K n i ≫ p) ≫ contraction K n hn p q h i =
      PolygonAtlas.torus K 1 0 := by
  rw [Category.assoc, Category.assoc, retained_contraction]
  rfl

/-- The target node is outside its actual Laurent open. -/
theorem targetNode_not_torus (x : Spec (.of K)) :
    (targetNode K).left x ∉ Set.range (PolygonAtlas.torus K 1 0).left :=
  PolygonNormalizationTorusPullback.node_not_torus K 1 (by decide)
    (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
    (PolygonAtlas.isPushout K 1 (by decide)) 0 0 x

/-- No omitted component or original node lies over the target Laurent open. -/
theorem contraction_torus_preimage :
    let _ := torus_isOpenImmersion K n hn p q h i
    (contraction K n hn p q h i).left ⁻¹ᵁ (PolygonAtlas.torus K 1 0).left.opensRange =
      (torusToComponent K ≫ componentι K n i ≫ p).left.opensRange := by
  let _ := torus_isOpenImmersion K n hn p q h i
  ext x
  change (contraction K n hn p q h i).left x ∈
    Set.range (PolygonAtlas.torus K 1 0).left ↔
      x ∈ Set.range (torusToComponent K ≫ componentι K n i ≫ p).left
  constructor
  · intro hx
    obtain ⟨j, y, rfl⟩ := PolygonComponentImages.cover K n hn p q h x
    by_cases hj : j = i
    · subst j
      have he := congrArg (fun f ↦ f.left y) (retained_contraction K n hn p q h i)
      change (contraction K n hn p q h i).left ((componentι K n i ≫ p).left y) =
        (retainedComponent K).left y at he
      rw [he] at hx
      have ht := PolygonNormalizationTorusPullback.torus_preimage K 1 (by decide)
        (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
        (PolygonAtlas.isPushout K 1 (by decide)) 0
      have hy : y ∈ Set.range (torusToComponent K).left :=
        (SetLike.ext_iff.mp ht y).mp hx
      obtain ⟨t, rfl⟩ := hy
      exact ⟨t, rfl⟩
    · have he := congrArg (fun f ↦ f.left y) (omitted_contraction K n hn p q h i hj)
      change (contraction K n hn p q h i).left ((componentι K n j ≫ p).left y) =
        (targetNode K).left ((componentToPoint K).left y) at he
      exact (targetNode_not_torus K _ (he ▸ hx)).elim
  · rintro ⟨t, rfl⟩
    exact ⟨t, (congrArg (fun f ↦ f.left t) (torus_contraction K n hn p q h i)).symm⟩

/-- The original Laurent component is the scheme-theoretic inverse image of the target torus. -/
theorem contraction_torus_square :
    IsPullback (𝟙 (MultiplicativeGroupScheme.gm K).left)
      (torusToComponent K ≫ componentι K n i ≫ p).left
      (PolygonAtlas.torus K 1 0).left (contraction K n hn p q h i).left := by
  let _ := torus_isOpenImmersion K n hn p q h i
  apply IsOpenImmersion.isPullback
  · rw [Category.id_comp]
    exact congrArg Over.Hom.left (torus_contraction K n hn p q h i)
  · exact contraction_torus_preimage K n hn p q h i

/-- Restriction of the original contraction to the target Laurent open is an isomorphism. -/
def contractionTorusIso : (MultiplicativeGroupScheme.gm K).left ≅
    pullback (PolygonAtlas.torus K 1 0).left (contraction K n hn p q h i).left :=
  (contraction_torus_square K n hn p q h i).isoPullback

/-- The restricted comparison is identity in the target Laurent coordinate. -/
@[reassoc] theorem contractionTorusIso_fst :
    (contractionTorusIso K n hn p q h i).hom ≫ pullback.fst _ _ =
      𝟙 (MultiplicativeGroupScheme.gm K).left :=
  (contraction_torus_square K n hn p q h i).isoPullback_hom_fst

/-- The other projection retains the actual original Laurent inclusion. -/
@[reassoc] theorem contractionTorusIso_snd :
    (contractionTorusIso K n hn p q h i).hom ≫ pullback.snd _ _ =
      (torusToComponent K ≫ componentι K n i ≫ p).left :=
  (contraction_torus_square K n hn p q h i).isoPullback_hom_snd

end FLT.Mazur.PolygonOneGonContraction
