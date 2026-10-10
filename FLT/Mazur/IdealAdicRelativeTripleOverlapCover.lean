/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeTripleRefinement
public import FLT.Mazur.ModuleSheafOpenImmersionGluing

/-!
# Affine covers of triple relative overlaps

Common ambient affine refinements cover the scheme-theoretic triple
intersection of relative tensor charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The scheme-theoretic intersection of three relative tensor charts. -/
def relativeTensorTripleOverlap (U V T : X.affineOpens) : Scheme.{u} :=
  Limits.pullback (relativeOverlapFirstProjection J f U V ≫ relativeTensorChart J f U)
    (relativeTensorChart J f T)

/-- Projection from the triple intersection to its first pair. -/
def relativeTripleFirstPairProjection (U V T : X.affineOpens) :
    relativeTensorTripleOverlap J f U V T ⟶ relativeTensorOverlap J f U V :=
  Limits.pullback.fst _ _

/-- Projection from the triple intersection to its third chart. -/
def relativeTripleThirdProjection (U V T : X.affineOpens) :
    relativeTensorTripleOverlap J f U V T ⟶ Spec (.of (RelativeAlgebra J f T)) :=
  Limits.pullback.snd _ _

/-- The first-pair projection is an open immersion. -/
instance relativeTripleFirstPairProjection_isOpenImmersion (U V T : X.affineOpens) :
    IsOpenImmersion (relativeTripleFirstPairProjection J f U V T) := by
  let _ := relativeTensorChart_isOpenImmersion J f T
  unfold relativeTripleFirstPairProjection
  infer_instance

/-- A common affine refinement maps canonically to the triple intersection. -/
def relativeTensorTripleOverlapChart {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    Spec (.of (RelativeAlgebra J f W)) ⟶ relativeTensorTripleOverlap J f U V T :=
  Limits.pullback.lift (relativeTensorOverlapChart J f i j) (relativeTensorTransition J f k)
    (by rw [← Category.assoc, relativeOverlapFirstProjection_chart,
      relativeTensorTransition_chart, relativeTensorTransition_chart])

/-- The triple chart restricts to the original chart of the first pair. -/
@[reassoc]
lemma relativeTensorTripleOverlapChart_firstPair {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    relativeTensorTripleOverlapChart J f i j k ≫ relativeTripleFirstPairProjection J f U V T =
      relativeTensorOverlapChart J f i j := Limits.pullback.lift_fst _ _ _

/-- The third coordinate of a triple chart is the original tensor transition. -/
@[reassoc]
lemma relativeTensorTripleOverlapChart_third {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    relativeTensorTripleOverlapChart J f i j k ≫ relativeTripleThirdProjection J f U V T =
      relativeTensorTransition J f k := Limits.pullback.lift_snd _ _ _

/-- Every common affine triple chart is an open immersion. -/
instance relativeTensorTripleOverlapChart_isOpenImmersion {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    IsOpenImmersion (relativeTensorTripleOverlapChart J f i j k) := by
  have : IsOpenImmersion (relativeTensorTripleOverlapChart J f i j k ≫
      relativeTripleFirstPairProjection J f U V T) := by
    rw [relativeTensorTripleOverlapChart_firstPair]
    infer_instance
  exact IsOpenImmersion.of_comp _ (relativeTripleFirstPairProjection J f U V T)

/-- Common affine triple charts jointly cover the whole scheme-theoretic triple overlap. -/
lemma relativeTensorTripleOverlapChart_jointly_surjective (U V T : X.affineOpens)
    (x : relativeTensorTripleOverlap J f U V T) :
    ∃ (W : X.affineOpens) (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1),
      x ∈ Set.range (relativeTensorTripleOverlapChart J f i j k) := by
  let _ := relativeTensorChart_isOpenImmersion J f U
  let _ := relativeTensorChart_isOpenImmersion J f V
  let p := relativeTripleFirstPairProjection J f U V T
  let q := relativeTripleThirdProjection J f U V T
  let a := relativeOverlapFirstProjection J f U V
  let b := relativeOverlapSecondProjection J f U V
  have ha : IsOpenImmersion a := by
    dsimp [a, relativeOverlapFirstProjection]
    infer_instance
  let z := relativeTensorChart J f U (a (p x))
  have hab : a ≫ relativeTensorChart J f U = b ≫ relativeTensorChart J f V :=
    Limits.pullback.condition
  have hpq : p ≫ a ≫ relativeTensorChart J f U = q ≫ relativeTensorChart J f T :=
    Limits.pullback.condition
  have hzU : z ∈ Set.range (relativeTensorChart J f U) := ⟨a (p x), rfl⟩
  have hzV : z ∈ Set.range (relativeTensorChart J f V) :=
    ⟨b (p x), (congrArg (fun g ↦ g (p x)) hab).symm⟩
  have hzT : z ∈ Set.range (relativeTensorChart J f T) :=
    ⟨q x, (congrArg (fun g ↦ g x) hpq).symm⟩
  obtain ⟨W, i, j, k, w, hw⟩ :=
    relativeTensorChart_exists_triple_refinement J f U V T z hzU hzV hzT
  refine ⟨W, i, j, k, w, ?_⟩
  apply p.isOpenEmbedding.injective
  apply a.isOpenEmbedding.injective
  apply (relativeTensorChart J f U).isOpenEmbedding.injective
  have hc : relativeTensorTripleOverlapChart J f i j k ≫ p ≫ a ≫
      relativeTensorChart J f U = relativeTensorChart J f W := by
    rw [relativeTensorTripleOverlapChart_firstPair_assoc]
    rw [← Category.assoc, relativeOverlapFirstProjection_chart, relativeTensorTransition_chart]
  exact (congrArg (fun g ↦ g w) hc).trans hw

/-- The open cover of the triple overlap by common affine refinements. -/
def relativeTensorTripleOverlapCover (U V T : X.affineOpens) :
    (relativeTensorTripleOverlap J f U V T).OpenCover where
  I₀ := {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1 ∧ W.1 ≤ T.1}
  X W := Spec (.of (RelativeAlgebra J f W.val))
  f W := relativeTensorTripleOverlapChart J f (homOfLE W.property.1)
    (homOfLE W.property.2.1) (homOfLE W.property.2.2)
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    obtain ⟨W, i, j, k, w, hw⟩ :=
      relativeTensorTripleOverlapChart_jointly_surjective J f U V T x
    exact ⟨⟨W, leOfHom i, leOfHom j, leOfHom k⟩, w, hw⟩

/-- Equality of linear maps on the triple overlap is detected on common affine charts. -/
lemma relativeTensorTripleOverlap_hom_ext (U V T : X.affineOpens)
    {M N : (relativeTensorTripleOverlap J f U V T).Modules} (a b : M ⟶ N)
    (h : ∀ (W : X.affineOpens) (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1),
      (Scheme.Modules.pullback (relativeTensorTripleOverlapChart J f i j k)).map a =
        (Scheme.Modules.pullback (relativeTensorTripleOverlapChart J f i j k)).map b) :
    a = b := by
  refine ModuleSheafOpenImmersionGluing.hom_ext
    (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1 ∧ W.1 ≤ T.1} ↦
      Spec (.of (RelativeAlgebra J f W.val)))
    (fun W ↦ relativeTensorTripleOverlapChart J f (homOfLE W.property.1)
      (homOfLE W.property.2.1) (homOfLE W.property.2.2)) ?_ a b ?_
  · intro x
    obtain ⟨W, i, j, k, hx⟩ := relativeTensorTripleOverlapChart_jointly_surjective J f U V T x
    exact ⟨⟨W, leOfHom i, leOfHom j, leOfHom k⟩, hx⟩
  · intro W
    exact h W.val (homOfLE W.property.1) (homOfLE W.property.2.1) (homOfLE W.property.2.2)

end FLT.Mazur.IdealAdicGradedPullback
