/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCommonRefinement

/-!
# Affine covers of full relative tensor overlaps

Common ambient affine refinements cover the scheme-theoretic overlap of
any two relative tensor charts. Their maps into the overlap commute
with every further affine refinement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The full scheme-theoretic overlap of two original relative tensor charts. -/
def relativeTensorOverlap (U V : X.affineOpens) : Scheme.{u} :=
  Limits.pullback (relativeTensorChart J f U) (relativeTensorChart J f V)

/-- A common affine refinement maps canonically into the full overlap. -/
def relativeTensorOverlapChart {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    (relativeTensorDiagram J f).obj W ⟶ relativeTensorOverlap J f U V :=
  Limits.pullback.lift (relativeTensorTransition J f i) (relativeTensorTransition J f j)
    ((relativeTensorTransition_chart J f i).trans
      (relativeTensorTransition_chart J f j).symm)

@[reassoc (attr := simp)]
lemma relativeTensorOverlapChart_fst {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeTensorOverlapChart J f i j ≫ Limits.pullback.fst _ _ =
      relativeTensorTransition J f i := Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativeTensorOverlapChart_snd {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeTensorOverlapChart J f i j ≫ Limits.pullback.snd _ _ =
      relativeTensorTransition J f j := Limits.pullback.lift_snd _ _ _

/-- Each overlap chart is an open immersion. -/
instance relativeTensorOverlapChart_isOpenImmersion {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    IsOpenImmersion (relativeTensorOverlapChart J f i j) := by
  let _ := relativeTensorChart_isOpenImmersion J f U
  let _ := relativeTensorChart_isOpenImmersion J f V
  have : IsOpenImmersion (relativeTensorOverlapChart J f i j ≫
      Limits.pullback.fst (relativeTensorChart J f U) (relativeTensorChart J f V)) := by
    rw [relativeTensorOverlapChart_fst]
    exact relativeTensorTransition_isOpenImmersion J f i
  exact IsOpenImmersion.of_comp _ (Limits.pullback.fst _ _)

/-- Maps of common affine refinements commute with their overlap charts. -/
@[reassoc]
lemma relativeTensorOverlapChart_refine {U V W Z : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : Z.1 ⟶ W.1) :
    relativeTensorTransition J f k ≫ relativeTensorOverlapChart J f i j =
      relativeTensorOverlapChart J f (k ≫ i) (k ≫ j) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, relativeTensorOverlapChart_fst, relativeTensorOverlapChart_fst,
      relativeTensorTransition_comp]
  · rw [Category.assoc, relativeTensorOverlapChart_snd, relativeTensorOverlapChart_snd,
      relativeTensorTransition_comp]

/-- Common affine refinements jointly cover every point of the full overlap. -/
lemma relativeTensorOverlapChart_jointly_surjective (U V : X.affineOpens)
    (x : relativeTensorOverlap J f U V) :
    ∃ (W : X.affineOpens) (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1),
      x ∈ Set.range (relativeTensorOverlapChart J f i j) := by
  let _ := relativeTensorChart_isOpenImmersion J f U
  let _ := relativeTensorChart_isOpenImmersion J f V
  let p := Limits.pullback.fst (relativeTensorChart J f U) (relativeTensorChart J f V)
  let q := Limits.pullback.snd (relativeTensorChart J f U) (relativeTensorChart J f V)
  have hx : relativeTensorChart J f U (p x) = relativeTensorChart J f V (q x) :=
    congrArg (fun g ↦ g x) (Limits.pullback.condition (f := relativeTensorChart J f U)
      (g := relativeTensorChart J f V))
  obtain ⟨r, s, hrs, hz⟩ := relativeTensorChart_exists_common_principal J f U V
    (relativeTensorChart J f U (p x)) ⟨p x, rfl⟩ ⟨q x, hx.symm⟩
  let W : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩
  let i : W.1 ⟶ U.1 := homOfLE (X.basicOpen_le r)
  let j : W.1 ⟶ V.1 := homOfLE (by
    change X.basicOpen r ≤ V.1
    rw [hrs]
    exact X.basicOpen_le s)
  obtain ⟨z, hz⟩ := hz
  refine ⟨W, i, j, z, ?_⟩
  apply p.isOpenEmbedding.injective
  apply (relativeTensorChart J f U).isOpenEmbedding.injective
  calc
    relativeTensorChart J f U (p (relativeTensorOverlapChart J f i j z)) =
        relativeTensorChart J f W z := by
      exact congrArg (fun g ↦ g z)
        ((relativeTensorOverlapChart_fst_assoc J f i j _).trans
          (relativeTensorTransition_chart J f i))
    _ = relativeTensorChart J f U (p x) := hz

/-- The actual open cover used for descending coefficient comparisons. -/
def relativeTensorOverlapCover (U V : X.affineOpens) :
    (relativeTensorOverlap J f U V).OpenCover where
  I₀ := {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1}
  X W := (relativeTensorDiagram J f).obj W.val
  f W := relativeTensorOverlapChart J f (homOfLE W.property.1) (homOfLE W.property.2)
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun W ↦ inferInstance⟩
    intro x
    obtain ⟨W, i, j, z, hz⟩ := relativeTensorOverlapChart_jointly_surjective J f U V x
    exact ⟨⟨W, leOfHom i, leOfHom j⟩, z, hz⟩

end FLT.Mazur.IdealAdicGradedPullback
