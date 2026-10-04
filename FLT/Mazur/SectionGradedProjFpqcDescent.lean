/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjCanonicalSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Fpqc descent of the canonical Proj open immersion

For a positively generated line bundle, being an open immersion for its
canonical section-ring Proj map can be checked after flat surjective affine
base change. The Cartesian square is proved from the section algebra.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjFpqcDescent
open FCurve SectionGradedProjConstruction SectionGradedProjCanonicalSquare
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{0}} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g] [Surjective g]
  (h : IsPullback p q f g) (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- Pullback preserves the line-bundle condition. -/
local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩

/-- The induced Proj projection is itself faithfully flat and quasi-compact. -/
lemma projection_fpqc :
    (Surjective (projection h L) ∧ Flat (projection h L)) ∧ QuasiCompact (projection h L) := by
  have he : Spec.map g.appTop = inv T.toSpecΓ ≫ g ≫ S.toSpecΓ := by
    rw [Scheme.toSpecΓ_naturality, IsIso.inv_hom_id_assoc]
  have hf : Flat (Spec.map g.appTop) := by rw [he]; infer_instance
  have hs : Surjective (Spec.map g.appTop) := by rw [he]; infer_instance
  have hq : QuasiCompact (Spec.map g.appTop) := inferInstance
  exact ⟨⟨MorphismProperty.of_isPullback (P := @Surjective)
      (structural_isPullback h L).flip hs,
    MorphismProperty.of_isPullback (P := @Flat) (structural_isPullback h L).flip hf⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) (structural_isPullback h L).flip hq⟩

include h in
/-- Open immersion of the actual canonical Proj map descends along flat surjective affine bases. -/
lemma isOpenImmersion_iff (hg : PositivePowerGenerated L) :
    IsOpenImmersion (toProj ((pullback p).obj L)
      (SectionGradedProjNaturality.positivePowerGenerated_pullback p L hg)) ↔
        IsOpenImmersion (toProj L hg) :=
  MorphismProperty.iff_of_isPullback (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (SectionGradedProjCanonicalSquare.isPullback h L hg).flip (projection_fpqc h L)

end FLT.Mazur.SectionGradedProjFpqcDescent
