/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesCommonRefinement

/-!
# Affine covers of full relative Rees overlaps

Common ambient affine refinements cover the scheme-theoretic overlap of
any two relative Rees charts. Their maps into the overlap commute
with every further affine refinement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

/-- The full scheme-theoretic overlap of two original relative Rees charts. -/
def modelOverlap (U V : X.affineOpens) : Scheme.{u} :=
  Limits.pullback (chartSpaceMap f J U) (chartSpaceMap f J V)

/-- A common affine refinement maps canonically into the full overlap. -/
def modelOverlapChart {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    (chartCover f J).X W ⟶ modelOverlap f J U V :=
  Limits.pullback.lift (modelMap f J i) (modelMap f J j)
    ((relativeRingRestriction_spec f J i).trans
      (relativeRingRestriction_spec f J j).symm)

@[reassoc (attr := simp)]
lemma modelOverlapChart_fst {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    modelOverlapChart f J i j ≫ Limits.pullback.fst _ _ =
      modelMap f J i := Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma modelOverlapChart_snd {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    modelOverlapChart f J i j ≫ Limits.pullback.snd _ _ =
      modelMap f J j := Limits.pullback.lift_snd _ _ _

/-- Each overlap chart is an open immersion. -/
instance modelOverlapChart_isOpenImmersion {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    IsOpenImmersion (modelOverlapChart f J i j) := by
  let _ := chartSpaceMap_isOpenImmersion f J U
  let _ := chartSpaceMap_isOpenImmersion f J V
  have : IsOpenImmersion (modelOverlapChart f J i j ≫
      Limits.pullback.fst (chartSpaceMap f J U) (chartSpaceMap f J V)) := by
    rw [modelOverlapChart_fst]
    exact modelMap_isOpenImmersion f J i
  exact IsOpenImmersion.of_comp _ (Limits.pullback.fst _ _)

/-- Maps of common affine refinements commute with their overlap charts. -/
@[reassoc]
lemma modelOverlapChart_refine {U V W Z : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : Z.1 ≤ W.1) :
    modelMap f J k ≫ modelOverlapChart f J i j =
      modelOverlapChart f J (k.trans i) (k.trans j) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, modelOverlapChart_fst, modelOverlapChart_fst,
      modelMap_comp]
  · rw [Category.assoc, modelOverlapChart_snd, modelOverlapChart_snd,
      modelMap_comp]

/-- Common affine refinements jointly cover every point of the full overlap. -/
lemma modelOverlapChart_jointly_surjective (U V : X.affineOpens)
    (x : modelOverlap f J U V) :
    ∃ (W : X.affineOpens) (i : W.1 ≤ U.1) (j : W.1 ≤ V.1),
      x ∈ Set.range (modelOverlapChart f J i j) := by
  let _ := chartSpaceMap_isOpenImmersion f J U
  let _ := chartSpaceMap_isOpenImmersion f J V
  let p := Limits.pullback.fst (chartSpaceMap f J U) (chartSpaceMap f J V)
  let q := Limits.pullback.snd (chartSpaceMap f J U) (chartSpaceMap f J V)
  have hx : chartSpaceMap f J U (p x) = chartSpaceMap f J V (q x) :=
    congrArg (fun g ↦ g x) (Limits.pullback.condition (f := chartSpaceMap f J U)
      (g := chartSpaceMap f J V))
  obtain ⟨r, s, hrs, hz⟩ := chartSpaceMap_exists_common_principal f J U V
    (chartSpaceMap f J U (p x)) ⟨p x, rfl⟩ ⟨q x, hx.symm⟩
  let W : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩
  let i : W.1 ≤ U.1 := X.basicOpen_le r
  let j : W.1 ≤ V.1 := by
    change X.basicOpen r ≤ V.1
    rw [hrs]
    exact X.basicOpen_le s
  obtain ⟨z, hz⟩ := hz
  refine ⟨W, i, j, z, ?_⟩
  apply p.isOpenEmbedding.injective
  apply (chartSpaceMap f J U).isOpenEmbedding.injective
  calc
    chartSpaceMap f J U (p (modelOverlapChart f J i j z)) =
        chartSpaceMap f J W z := by
      exact congrArg (fun g ↦ g z)
        ((modelOverlapChart_fst_assoc f J i j _).trans
          (relativeRingRestriction_spec f J i))
    _ = chartSpaceMap f J U (p x) := hz

/-- The actual open cover used for descending coefficient comparisons. -/
def modelOverlapCover (U V : X.affineOpens) :
    (modelOverlap f J U V).OpenCover where
  I₀ := {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1}
  X W := (chartCover f J).X W.val
  f W := modelOverlapChart f J W.property.1 W.property.2
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun W ↦ inferInstance⟩
    intro x
    obtain ⟨W, i, j, z, hz⟩ := modelOverlapChart_jointly_surjective f J U V x
    exact ⟨⟨W, i, j⟩, z, hz⟩

end FLT.Mazur.BaseAdicRees
