/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteFiberInvariants
public import FLT.Mazur.AffineHilbertAdmissibleKernelOpen
public import FLT.Mazur.SchemeKernelFlatSourceImage

/-!
# Actual old finite target neighborhoods from admissible source coefficients

Take the image of an admissible original principal over the constructed
whole-source flat locus. Saturation proves that its entire OLD kernel has
an actual original inverse. Its complete original source is fppf over this
open. This works at every such fiber, without an integral source, generic
point, split branch or globally flat projection hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
variable (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)

/-- The constructed open lies in the unchanged old finite coefficient scheme. -/
def admissibleFlatImage : (T).Opens := SchemeFlatSourceImage.image v (A.left.basicOpen s.val)

local notation "W" => admissibleFlatImage f hL d V c k s

/-- Its complete original source has a flat projection, without a global flatness input. -/
theorem admissibleFlatImage_flat : Flat (pullback.snd v (W).ι) :=
  SchemeFlatSourceImage.projection_flat v (A.left.basicOpen s.val)

/-- Every target point has an actual original source, including nonsplit branches. -/
theorem admissibleFlatImage_surjective : Surjective (pullback.snd v (W).ι) :=
  SchemeFlatSourceImage.projection_surjective v (A.left.basicOpen s.val)

/-- Saturation makes the complete retained source lie in the original principal open. -/
theorem admissibleFlatImage_source_le : v ⁻¹ᵁ W ≤ A.left.basicOpen s.val :=
  SchemeFlatSourceImage.preimage_le v (A.left.basicOpen s.val)
    (finiteFiber_principal_mem_iff f hL d V c k s)

/-- Every admissible point over the whole-source flat locus lies in this actual target open. -/
theorem admissibleFlatImage_contains (x : A.left) (hx : x ∈ A.left.basicOpen s.val)
    (hf : v x ∈ SchemeFlatTargetOpen.locus v) : v x ∈ W :=
  SchemeFlatSourceImage.contains v (A.left.basicOpen s.val) x hx hf

variable [IsAffine V.left] (hs : s ∈ invariantEnvelopeDenominators f hL d V c k)

include hs in
/-- The old effective target contains the whole constructed open, beyond the generic fiber. -/
theorem admissibleFlatImage_le_effective : W ≤ KernelPairEffectiveOpen.targetOpen p q v h :=
  SchemeKernelFlatSourceImage.image_le_effective p q v h (A.left.basicOpen s.val)
    (finiteFiber_principal_mem_iff f hL d V c k s)
    (admissibleOriginalKernel_le_inverseLocus f hL d V c k s hs)

include hs in
/-- Tests keep the full original relation, not just equality of topological coefficient points. -/
theorem admissibleFlatImage_original_test {Z : Scheme} (a b : Z ⟶ A.left)
    (hab : a ≫ v = b ≫ v) (ha : Set.range (a ≫ v) ⊆ W) :
    ∃! z : Z ⟶ (relation f hL d V c k).left, z ≫ p = a ∧ z ≫ q = b := by
  let _ : Mono (pullback.lift p q h) := modelRelationKernelMap_mono f hL d V c k v h
  exact SchemeKernelFlatSourceImage.original_test_lift p q v h (A.left.basicOpen s.val)
    (finiteFiber_principal_mem_iff f hL d V c k s)
    (admissibleOriginalKernel_le_inverseLocus f hL d V c k s hs) a b hab ha

end FLT.Mazur.HilbertChart.AffineRestriction
