/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelImageRestriction
public import FLT.Mazur.AffineHilbertNestedRestriction
public import FLT.Mazur.SchemeRelationInvariantDomainIso

/-!
# The full original Picard relation over the finite model image open

The constructed source is saturated under every original Picard arrow.
Its full two-endpoint relation is exactly one open in the original relation,
and its projection retains the original candidate-kernel tests on all schemes.
The comparison to that kernel remains a monomorphism, not a claimed isomorphism.
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
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "W" => finiteModelImageSourceOpen f hL d V c k
local notation "j" => finiteModelImageSourceMap f hL d V c k
local notation "u" => finiteModelImageProjection f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
local notation "i" => finiteModelImageTargetMap f hL d V c k

/-- No original relation arrow leaves the constructed source once either endpoint lies in it. -/
theorem finiteModelImageSourceOpen_invariant : (p).left ⁻¹ᵁ W = (q).left ⁻¹ᵁ W := by
  have he : (p).left ≫ (v).left = (q).left ≫ (v).left :=
    congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
  change (p).left ⁻¹ᵁ ((v).left ⁻¹ᵁ finiteModelImageInterior f hL d V c k) =
    (q).left ⁻¹ᵁ ((v).left ⁻¹ᵁ finiteModelImageInterior f hL d V c k)
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, he]

/-- The actual selected parameter remains an open restriction of the original parameter. -/
instance finiteModelImageChart_isOpenImmersion : IsOpenImmersion (j ≫ k).left := by
  change IsOpenImmersion ((W).ι ≫ k.left)
  infer_instance

/-- The entire restricted Picard relation is an actual open of the original relation scheme. -/
def finiteModelImageFullRelationIso : (relation f hL d V c (j ≫ k)).left ≅
    ((p).left ⁻¹ᵁ W).toScheme :=
  nestedSchemeDoubleIso f hL d V c k j ≪≫
    SchemeRelationRestriction.invariantDomainIso (p).left (q).left W
      (finiteModelImageSourceOpen_invariant f hL d V c k)

/-- The isomorphism keeps the unchanged original relation arrow. -/
@[reassoc]
theorem finiteModelImageFullRelationIso_hom_ι :
    (finiteModelImageFullRelationIso f hL d V c k).hom ≫ ((p).left ⁻¹ᵁ W).ι =
      (nestedToFullRelation f hL d V c k j).left := by
  dsimp only [finiteModelImageFullRelationIso, Iso.trans_hom]
  rw [Category.assoc, SchemeRelationRestriction.invariantDomainIso_hom_ι]
  exact nestedSchemeDoubleIso_arrow f hL d V c k j

/-- The full original arrow comparison is an open immersion after restriction. -/
instance finiteModelImageRelation_isOpenImmersion :
    IsOpenImmersion (nestedToFullRelation f hL d V c k j).left := by
  rw [← finiteModelImageFullRelationIso_hom_ι f hL d V c k]
  infer_instance

/-- Equality in the constructed open target retains both original candidate endpoint maps. -/
theorem finiteModelImageProjection_test_iff {T : Over (Spec (.of R))}
    (a b : T ⟶ finiteModelImageSource f hL d V c k) :
    a ≫ u = b ≫ u ↔
      (a ≫ j) ≫ invariantAffineProjection f hL d V c k =
        (b ≫ j) ≫ invariantAffineProjection f hL d V c k := by
  let _ : Mono (i).left :=
    inferInstanceAs (Mono (finiteModelImageInterior f hL d V c k).ι)
  let _ : Mono i := Over.mono_of_mono_left i
  rw [← cancel_mono i, Category.assoc, Category.assoc,
    finiteModelImageProjection_square, ← Category.assoc, ← Category.assoc]
  exact finiteKernelProjection_test_iff f hL d V c k (a ≫ j) (b ≫ j)

local notation "r" => fst f hL d V c (j ≫ k)
local notation "s" => snd f hL d V c (j ≫ k)

/-- The full original Picard relation is coequalized by the actual surjective restriction. -/
@[reassoc]
theorem finiteModelImageProjection_condition : r ≫ u = s ≫ u := by
  apply (finiteModelImageProjection_test_iff f hL d V c k r s).mpr
  rw [← nestedToFullRelation_fst, ← nestedToFullRelation_snd,
    Category.assoc, Category.assoc, invariantAffineProjection_condition]

/-- The unchanged full Picard relation maps into the actual restricted projection kernel. -/
def finiteModelImageKernelMap : relation f hL d V c (j ≫ k) ⟶ pullback u u :=
  pullback.lift r s (finiteModelImageProjection_condition f hL d V c k)

/-- The comparison loses no original arrows; surjectivity is still unproved. -/
instance finiteModelImageKernelMap_mono : Mono (finiteModelImageKernelMap f hL d V c k) where
  right_cancellation a b h := by
    apply hom_ext f hL d V c (j ≫ k)
    · simpa only [finiteModelImageKernelMap, Category.assoc, pullback.lift_fst] using
        congrArg (fun t ↦ t ≫ pullback.fst u u) h
    · simpa only [finiteModelImageKernelMap, Category.assoc, pullback.lift_snd] using
        congrArg (fun t ↦ t ≫ pullback.snd u u) h

end FLT.Mazur.HilbertChart.AffineRestriction
