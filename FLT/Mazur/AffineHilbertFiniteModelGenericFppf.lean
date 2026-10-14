/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelImage
public import FLT.Mazur.SchemeGenericFppfTargetOpen
public import FLT.Mazur.RelativeFppfTargetOpen

/-!
# Nonempty fppf regions of finite models selected from integral sources

An integral original parameter chart makes its actual finite invariant
coefficient model integral. Dominance was proved from the literal coefficient
inclusion. Generic flatness now proves a dense nonempty fppf region of this
unchanged model. Identifying its kernel with the full Picard relation remains
separate; this module does not assert effective Picard descent on that region.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left] [IsIntegral A.left]
local notation "v" => finiteKernelProjection f hL d V c k
local notation "Q" => finiteKernelModel f hL d V c k

/-- Integrality comes from the original chart, via the actual coefficient inclusion. -/
instance finiteKernelModel_isIntegral : IsIntegral (Q).left := by
  change IsIntegral (Spec (.of (finiteKernelCoefficientAlgebra f hL d V c k)))
  infer_instance

/-- The actual finite model's full-source fppf region is dense. -/
theorem finiteModelFppfLocus_dense :
    Dense (SchemeFppfTargetOpen.locus (v).left : Set (Q).left) :=
  SchemeFppfTargetOpen.dense (v).left

/-- Generic flatness proves actual nonemptiness, with no flat model premise. -/
theorem finiteModelFppfLocus_nonempty :
    (SchemeFppfTargetOpen.locus (v).left : Set (Q).left).Nonempty :=
  SchemeFppfTargetOpen.nonempty (v).left

/-- Every nonempty open of the actual model contains an original source image in this region. -/
theorem finiteModelFppfLocus_hits (U : (Q).left.Opens) (hU : (U : Set (Q).left).Nonempty) :
    ∃ x : A.left, (v).left x ∈ U ∧ (v).left x ∈ SchemeFppfTargetOpen.locus (v).left :=
  SchemeFppfTargetOpen.exists_source (v).left U hU

/-- The actual relative fppf target has an original model point. -/
theorem finiteModelGenericFppfTarget_nonempty :
    Nonempty (RelativeFppfTargetOpen.target v).left := by
  obtain ⟨y, hy⟩ := finiteModelFppfLocus_nonempty f hL d V c k
  exact ⟨⟨y, hy⟩⟩

/-- Its full relative source is nonempty and still lies over the original coefficient base. -/
theorem finiteModelGenericFppfSource_nonempty :
    Nonempty (RelativeFppfTargetOpen.source v).left :=
  SchemeFppfTargetOpen.source_nonempty (v).left

end FLT.Mazur.HilbertChart.AffineRestriction
