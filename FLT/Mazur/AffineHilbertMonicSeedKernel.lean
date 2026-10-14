/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNestedKernel
public import FLT.Mazur.AffineHilbertMonicSeedCharts

/-!
# Recomputed full Picard kernels on monic-seed chart selections

The complete Picard relation recomputed on a selected chart is the actual
coefficient kernel. This combines original-arrow division with the nested
relation isomorphism, and applies to the constructed affine open charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
attribute [local irreducible] relation fst snd
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  {T Z : Scheme} (w : A.left ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w = (snd f hL d V c k).left ≫ w)
  (a : Z ⟶ A.left) [Mono (a ≫ w)]
local notation "p₀" => fst f hL d V c k
local notation "q₀" => snd f hL d V c k

include hw in
/-- Recomputing the full relation on a selection preserves the constructed kernel equality. -/
theorem monicSeedSelection_isPullback {B : Over (Spec (.of R))} (v : B ⟶ A)
    (t : B.left ⟶ pullback (q₀).left a)
    (ht : t ≫ SchemeRelationEtaleBranchPropagation.branch (p₀).left (q₀).left a = v.left) :
    IsPullback (fst f hL d V c (v ≫ k)).left (snd f hL d V c (v ≫ k)).left
      (v.left ≫ w) (v.left ≫ w) := by
  let _ : Mono (pullback.lift (p₀).left (q₀).left hw) :=
    modelRelationKernelMap_mono f hL d V c k w hw
  exact nested_isPullback f hL d V c k v _
    (SchemeRelationMonicSeedKernel.selection_isPullback
      (equivalence f hL d V c k) w hw a v.left t ht)

variable (z : (pullback (snd f hL d V c k).left a : Scheme))
local notation "v" => monicSeedAffineMap f hL d V c k a z

include hw in
/-- The actual constructed affine chart has its full recomputed original kernel. -/
theorem monicSeedAffine_isPullback :
    IsPullback (fst f hL d V c (v ≫ k)).left (snd f hL d V c (v ≫ k)).left
      ((v).left ≫ w) ((v).left ≫ w) :=
  monicSeedSelection_isPullback f hL d V c k w hw a v
    (SchemeRelationMonicSeedKernel.affineToBranch (p := p₀) a z) rfl

end FLT.Mazur.HilbertChart.AffineRestriction
