/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertInvariantAffineModel
public import FLT.Mazur.VariableHilbertNoetherianSource
public import FLT.Mazur.SchemeRelationInvariantDominant

/-!
# Finite type of the original invariant candidate projection

The original parameter structure map is locally of finite type. Factoring it
through the actual invariant spectrum proves finite type of the projection,
without requiring Noetherianity of the invariant ring. Its image is dense.
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
local notation "v" => invariantAffineProjection f hL d V c k

include k in
omit [IsAffine A.left] in
/-- The original parameter structure map retains local finite type on the selected source. -/
theorem selectedSource_locallyOfFiniteType : LocallyOfFiniteType A.hom := by
  rw [← k.w]
  infer_instance

/-- Factorization of the original base map proves local finite type over full invariants. -/
instance invariantAffineProjection_locallyOfFiniteType : LocallyOfFiniteType (v).left := by
  have h : LocallyOfFiniteType ((v).left ≫ (invariantAffineModel f hL d V c k).hom) := by
    rw [(v).w]
    exact selectedSource_locallyOfFiniteType f d V k
  exact locallyOfFiniteType_of_comp (v).left (invariantAffineModel f hL d V c k).hom

/-- The actual projection is quasi-compact, since both its source and target are affine. -/
instance invariantAffineProjection_quasiCompact : QuasiCompact (v).left := by
  infer_instance

/-- The coefficient inclusion is a finite type ring map without a Noetherian invariant ring. -/
theorem invariantAffineProjection_finiteType_appTop : (v).left.appTop.hom.FiniteType :=
  HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance

/-- Every nonempty target open meets the original parameter image. -/
instance invariantAffineProjection_isDominant : IsDominant (v).left :=
  SchemeRelationInvariantSpectrum.projection_isDominant _ _

end FLT.Mazur.HilbertChart.AffineRestriction
