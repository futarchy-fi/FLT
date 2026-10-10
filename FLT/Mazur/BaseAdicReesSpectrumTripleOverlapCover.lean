/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumTripleRefinement
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

attribute [local semireducible] FLT.Mazur.BaseAdicRees.modelSpectrum

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

/-- The scheme-theoretic intersection of three relative tensor charts. -/
def spectrumTripleOverlap (U V T : X.affineOpens) : Scheme.{u} :=
  Limits.pullback (spectrumOverlapFirst f J U V ≫ spectrumSpaceMap f J U)
    (spectrumSpaceMap f J T)

/-- Projection from the triple intersection to its first pair. -/
def spectrumTripleFirstPairProjection (U V T : X.affineOpens) :
    spectrumTripleOverlap f J U V T ⟶ modelOverlap f J U V :=
  Limits.pullback.fst _ _

/-- Projection from the triple intersection to its third chart. -/
def spectrumTripleThirdProjection (U V T : X.affineOpens) :
    spectrumTripleOverlap f J U V T ⟶ modelSpectrum f J T :=
  Limits.pullback.snd _ _

/-- The first-pair projection is an open immersion. -/
instance spectrumTripleFirstPairProjection_isOpenImmersion (U V T : X.affineOpens) :
    IsOpenImmersion (spectrumTripleFirstPairProjection f J U V T) := by
  let _ := spectrumSpaceMap_isOpenImmersion f J T
  unfold spectrumTripleFirstPairProjection
  infer_instance

/-- A common affine refinement maps canonically to the triple intersection. -/
def spectrumTripleOverlapChart {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    modelSpectrum f J W ⟶ spectrumTripleOverlap f J U V T :=
  Limits.pullback.lift (spectrumOverlapChart f J i j) (spectrumMap f J k)
    (by rw [← Category.assoc, spectrumOverlapChart_first,
      spectrumMap_chart, spectrumMap_chart])

/-- The triple chart restricts to the original chart of the first pair. -/
@[reassoc]
lemma spectrumTripleOverlapChart_firstPair {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    spectrumTripleOverlapChart f J i j k ≫ spectrumTripleFirstPairProjection f J U V T =
      spectrumOverlapChart f J i j := Limits.pullback.lift_fst _ _ _

/-- The third coordinate of a triple chart is the original tensor transition. -/
@[reassoc]
lemma spectrumTripleOverlapChart_third {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    spectrumTripleOverlapChart f J i j k ≫ spectrumTripleThirdProjection f J U V T =
      spectrumMap f J k := Limits.pullback.lift_snd _ _ _

/-- Every common affine triple chart is an open immersion. -/
instance spectrumTripleOverlapChart_isOpenImmersion {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    IsOpenImmersion (spectrumTripleOverlapChart f J i j k) := by
  have : IsOpenImmersion (spectrumTripleOverlapChart f J i j k ≫
      spectrumTripleFirstPairProjection f J U V T) := by
    rw [spectrumTripleOverlapChart_firstPair]
    infer_instance
  exact IsOpenImmersion.of_comp _ (spectrumTripleFirstPairProjection f J U V T)

/-- Common affine triple charts jointly cover the whole scheme-theoretic triple overlap. -/
lemma spectrumTripleOverlapChart_jointly_surjective (U V T : X.affineOpens)
    (x : spectrumTripleOverlap f J U V T) :
    ∃ (W : X.affineOpens) (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1),
      x ∈ Set.range (spectrumTripleOverlapChart f J i j k) := by
  let _ := chartSpaceMap_isOpenImmersion f J U
  let _ := chartSpaceMap_isOpenImmersion f J V
  let p := spectrumTripleFirstPairProjection f J U V T
  let q := spectrumTripleThirdProjection f J U V T
  let a := spectrumOverlapFirst f J U V
  let b := spectrumOverlapSecond f J U V
  have ha : IsOpenImmersion a := by
    change IsOpenImmersion (Limits.pullback.fst
      (chartSpaceMap f J U) (chartSpaceMap f J V))
    infer_instance
  let z := spectrumSpaceMap f J U (a (p x))
  have hab : a ≫ spectrumSpaceMap f J U = b ≫ spectrumSpaceMap f J V :=
    spectrumOverlap_condition f J U V
  have hpq : p ≫ a ≫ spectrumSpaceMap f J U = q ≫ spectrumSpaceMap f J T :=
    Limits.pullback.condition
  have hzU : z ∈ Set.range (spectrumSpaceMap f J U) := ⟨a (p x), rfl⟩
  have hzV : z ∈ Set.range (spectrumSpaceMap f J V) :=
    ⟨b (p x), (congrArg (fun g ↦ g (p x)) hab).symm⟩
  have hzT : z ∈ Set.range (spectrumSpaceMap f J T) :=
    ⟨q x, (congrArg (fun g ↦ g x) hpq).symm⟩
  obtain ⟨W, i, j, k, w, hw⟩ :=
    spectrumSpaceMap_exists_triple_refinement f J U V T z hzU hzV hzT
  refine ⟨W, i, j, k, w, ?_⟩
  apply p.isOpenEmbedding.injective
  apply a.isOpenEmbedding.injective
  apply (spectrumSpaceMap f J U).isOpenEmbedding.injective
  have hc : spectrumTripleOverlapChart f J i j k ≫ p ≫ a ≫
      spectrumSpaceMap f J U = spectrumSpaceMap f J W := by
    rw [spectrumTripleOverlapChart_firstPair_assoc]
    rw [← Category.assoc, spectrumOverlapChart_first, spectrumMap_chart]
  exact (congrArg (fun g ↦ g w) hc).trans hw

/-- The open cover of the triple overlap by common affine refinements. -/
def spectrumTripleOverlapCover (U V T : X.affineOpens) :
    (spectrumTripleOverlap f J U V T).OpenCover where
  I₀ := {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1 ∧ W.1 ≤ T.1}
  X W := modelSpectrum f J W.val
  f W := spectrumTripleOverlapChart f J W.property.1
    W.property.2.1 W.property.2.2
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    obtain ⟨W, i, j, k, w, hw⟩ :=
      spectrumTripleOverlapChart_jointly_surjective f J U V T x
    exact ⟨⟨W, i, j, k⟩, w, hw⟩

/-- Equality of linear maps on the triple overlap is detected on common affine charts. -/
lemma spectrumTripleOverlap_hom_ext (U V T : X.affineOpens)
    {M N : (spectrumTripleOverlap f J U V T).Modules} (a b : M ⟶ N)
    (h : ∀ (W : X.affineOpens) (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1),
      (Scheme.Modules.pullback (spectrumTripleOverlapChart f J i j k)).map a =
        (Scheme.Modules.pullback (spectrumTripleOverlapChart f J i j k)).map b) :
    a = b := by
  refine ModuleSheafOpenImmersionGluing.hom_ext
    (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1 ∧ W.1 ≤ T.1} ↦
      modelSpectrum f J W.val)
    (fun W ↦ spectrumTripleOverlapChart f J W.property.1
      W.property.2.1 W.property.2.2) ?_ a b ?_
  · intro x
    obtain ⟨W, i, j, k, hx⟩ := spectrumTripleOverlapChart_jointly_surjective f J U V T x
    exact ⟨⟨W, i, j, k⟩, hx⟩
  · intro W
    exact h W.val W.property.1 W.property.2.1 W.property.2.2

end FLT.Mazur.BaseAdicRees
