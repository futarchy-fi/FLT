/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelSourceBranchCoverage
public import FLT.Mazur.SchemeRelationMonicSeedAffine

/-!
# Actual affine Hilbert selections from monic coefficient seeds

The proper-family relation and a two-sided etale monic seed construct affine
open Hilbert parameter charts through all points of its propagated orbit.
Their coefficient maps are etale on the entire selected source. Seed existence
and coverage of all original classes remain separate geometric questions.
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
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "p₀" => fst f hL d V c k
local notation "q₀" => snd f hL d V c k
variable {Z : Scheme} (a : Z ⟶ A.left)
  (z : (pullback (snd f hL d V c k).left a : Scheme))

/-- The affine source is constructed from the original relation and source seed. -/
def monicSeedAffineSource : Over (Spec (.of R)) :=
  SchemeRelationMonicSeedKernel.affineSource (p := p₀) a z

/-- The selected affine source retains its original relative source map. -/
def monicSeedAffineMap : monicSeedAffineSource f hL d V c k a z ⟶ A :=
  SchemeRelationMonicSeedKernel.affineMap (p := p₀) a z

/-- The newly selected Hilbert chart is an actual original parameter morphism. -/
def monicSeedAffineChart : monicSeedAffineSource f hL d V c k a z ⟶
    variableHilbertTest f d V := monicSeedAffineMap f hL d V c k a z ≫ k

instance monicSeedAffineSource_isAffine : IsAffine (monicSeedAffineSource f hL d V c k a z).left :=
  inferInstanceAs (IsAffine (SchemeRelationMonicSeedKernel.affineSource (p := p₀) a z).left)

/-- The affine selection contains a point over the specified original orbit point. -/
def monicSeedAffinePoint : (monicSeedAffineSource f hL d V c k a z).left :=
  SchemeRelationMonicSeedKernel.affinePoint (p := p₀) a z

omit [Etale V.hom] [IsOpenImmersion k.left] in
/-- The chosen point retains its literal image in the original Hilbert parameter. -/
theorem monicSeedAffinePoint_chart : (monicSeedAffineChart f hL d V c k a z).left
    (monicSeedAffinePoint f hL d V c k a z) =
      k.left (SchemeRelationEtaleBranchPropagation.branch (p₀).left (q₀).left a z) :=
  congrArg k.left (SchemeRelationMonicSeedKernel.affinePoint_original (p := p₀) a z)

variable {T : Scheme} (w : A.left ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w = (snd f hL d V c k).left ≫ w)
  [Mono (a ≫ w)]

include hw in
/-- Monicity is derived from the full original Picard relation, not assumed for the selection. -/
theorem monicSeedAffineMap_isOpenImmersion [Etale a] :
    IsOpenImmersion (monicSeedAffineMap f hL d V c k a z).left := by
  let _ : Mono (pullback.lift (p₀).left (q₀).left hw) :=
    modelRelationKernelMap_mono f hL d V c k w hw
  exact SchemeRelationMonicSeedKernel.affineMap_isOpenImmersion w hw a z

include hw in
/-- These are genuine affine open parameter charts for recomputing finite coefficient models. -/
theorem monicSeedAffineChart_isOpenImmersion [Etale a] :
    IsOpenImmersion (monicSeedAffineChart f hL d V c k a z).left := by
  let _ := monicSeedAffineMap_isOpenImmersion f hL d V c k a z w hw
  exact inferInstanceAs
    (IsOpenImmersion ((monicSeedAffineMap f hL d V c k a z).left ≫ k.left))

include hw in
omit [Mono (a ≫ w)] in
/-- The whole selected affine source remains etale over the unchanged coefficient model. -/
theorem monicSeedAffineChart_target_etale [Etale (a ≫ w)] :
    Etale ((monicSeedAffineMap f hL d V c k a z).left ≫ w) :=
  SchemeRelationMonicSeedKernel.affineMap_target_etale w hw a z

end FLT.Mazur.HilbertChart.AffineRestriction
