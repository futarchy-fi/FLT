/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertClosedPatchRefinement

/-!
# Full original relation maps along closed patch refinements

The actual quotient-ring refinement carries the original Picard section and
all relation arrows. Its relation comparison is itself a closed base change
of either full endpoint, including infinitesimal and residual closed patches.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "Q" => finiteKernelModel f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
variable (r : Γ((finiteKernelModel f hL d V c k).left, ⊤))
local notation "U" => Scheme.basicOpen (Over.left Q) r
local notation "g" => finiteModelPrincipalProjection f hL d V c k r
variable {J K : Ideal Γ(((finiteKernelModel f hL d V c k).left.basicOpen r).toScheme, ⊤)}
  (hJK : J ≤ K)
local notation "iJ" => finiteModelStratumMap f hL d V c k r J
local notation "iK" => finiteModelStratumMap f hL d V c k r K

local notation "uJ" => finiteModelClosedPatchSourceMap f hL d V c k r J
local notation "uK" => finiteModelClosedPatchSourceMap f hL d V c k r K
local notation "s" => finiteModelClosedSourceRefinement f hL d V c k r hJK
local notation "pJ" => fst f hL d V c (uJ ≫ k)
local notation "pK" => fst f hL d V c (uK ≫ k)
local notation "qJ" => snd f hL d V c (uJ ≫ k)
local notation "qK" => snd f hL d V c (uK ≫ k)
local notation "aJ" => nestedToFullRelation f hL d V c k uJ
local notation "aK" => nestedToFullRelation f hL d V c k uK

/-- The section on the smaller closed source is exactly the original Picard section pulled back. -/
theorem finiteModelClosedRefinement_section :
    (relativeFppfSheaf f).obj.map (s).op (sectionAt f hL d V c (uJ ≫ k)) =
      sectionAt f hL d V c (uK ≫ k) := by
  simp only [sectionAt, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rw [← Category.assoc, finiteModelClosedSourceRefinement_original]

/-- Every original Picard arrow over the smaller patch determines an arrow over the larger one. -/
def finiteModelClosedRefinementRelationMap : relation f hL d V c (uK ≫ k) ⟶
    relation f hL d V c (uJ ≫ k) :=
  arrow f hL d V c (uJ ≫ k) (pK ≫ s) (qK ≫ s) (by
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      finiteModelClosedRefinement_section]
    exact equal_class f hL d V c (uK ≫ k))

local notation "α" => finiteModelClosedRefinementRelationMap f hL d V c k r hJK

/-- The original first endpoint is retained under closed refinement. -/
@[reassoc]
theorem finiteModelClosedRefinementRelationMap_fst : α ≫ pJ = pK ≫ s :=
  arrow_fst f hL d V c (uJ ≫ k) _ _ _

/-- The original second endpoint is retained independently. -/
@[reassoc]
theorem finiteModelClosedRefinementRelationMap_snd : α ≫ qJ = qK ≫ s :=
  arrow_snd f hL d V c (uJ ≫ k) _ _ _

/-- Refinement leaves the underlying original Picard relation arrow unchanged. -/
@[reassoc]
theorem finiteModelClosedRefinementRelationMap_original : α ≫ aJ = aK := by
  apply hom_ext f hL d V c k
  · rw [Category.assoc, nestedToFullRelation_fst, ← Category.assoc,
      finiteModelClosedRefinementRelationMap_fst, Category.assoc,
      finiteModelClosedSourceRefinement_original, nestedToFullRelation_fst]
  · rw [Category.assoc, nestedToFullRelation_snd, ← Category.assoc,
      finiteModelClosedRefinementRelationMap_snd, Category.assoc,
      finiteModelClosedSourceRefinement_original, nestedToFullRelation_snd]

/-- The full first-endpoint relation square is the actual closed source base change. -/
theorem finiteModelClosedRefinementRelationMap_fst_isPullback :
    IsPullback (α).left (pK).left (pJ).left (s).left := by
  have hJ := monicModelRelation_fst_isPullback f hL d V c k uJ
    (finiteModelClosedPatchToModel f hL d V c k r J) (pullback.snd g iJ)
    (finiteModelClosedPatchSource_isPullback f hL d V c k r J)
  have hK := monicModelRelation_fst_isPullback f hL d V c k uK
    (finiteModelClosedPatchToModel f hL d V c k r K) (pullback.snd g iK)
    (finiteModelClosedPatchSource_isPullback f hL d V c k r K)
  have hα := congrArg Over.Hom.left
    (finiteModelClosedRefinementRelationMap_original f hL d V c k r hJK)
  have hs := congrArg Over.Hom.left
    (finiteModelClosedSourceRefinement_original f hL d V c k r hJK)
  rw [← hα, ← hs] at hK
  exact hK.of_right
    (congrArg Over.Hom.left (finiteModelClosedRefinementRelationMap_fst f hL d V c k r hJK)) hJ

/-- The full second-endpoint relation square is the actual closed source base change. -/
theorem finiteModelClosedRefinementRelationMap_snd_isPullback :
    IsPullback (α).left (qK).left (qJ).left (s).left := by
  have hJ := monicModelRelation_snd_isPullback f hL d V c k uJ
    (finiteModelClosedPatchToModel f hL d V c k r J) (pullback.snd g iJ)
    (finiteModelClosedPatchSource_isPullback f hL d V c k r J)
  have hK := monicModelRelation_snd_isPullback f hL d V c k uK
    (finiteModelClosedPatchToModel f hL d V c k r K) (pullback.snd g iK)
    (finiteModelClosedPatchSource_isPullback f hL d V c k r K)
  have hα := congrArg Over.Hom.left
    (finiteModelClosedRefinementRelationMap_original f hL d V c k r hJK)
  have hs := congrArg Over.Hom.left
    (finiteModelClosedSourceRefinement_original f hL d V c k r hJK)
  rw [← hα, ← hs] at hK
  exact hK.of_right
    (congrArg Over.Hom.left (finiteModelClosedRefinementRelationMap_snd f hL d V c k r hJK)) hJ

/-- The full original relation embeds as the actual closed subscheme above the refined source. -/
instance finiteModelClosedRefinementRelationMap_isClosedImmersion :
    IsClosedImmersion (α).left :=
  MorphismProperty.of_isPullback
    (finiteModelClosedRefinementRelationMap_fst_isPullback f hL d V c k r hJK).flip
    inferInstance

end FLT.Mazur.HilbertChart.AffineRestriction
