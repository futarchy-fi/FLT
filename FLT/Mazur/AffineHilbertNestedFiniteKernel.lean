/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNestedFiniteModel
public import FLT.Mazur.AffineHilbertMonicSeedKernel

/-!
# Effectivity survives actual finite coefficient recomputation on seed charts

On a selection inside a propagated monic seed, the joint target keeps the
old coefficients and the full newly computed finite coefficient algebra.
Its kernel is precisely the freshly recomputed original Picard relation.
No flatness or global coverage of this joint projection is inferred here.
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
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {B : Over (Spec (.of R))} [IsAffine B.left] (v : B ⟶ A) [IsOpenImmersion v.left]
local notation "p" => Over.Hom.left (fst f hL d V c (v ≫ k))
local notation "q" => Over.Hom.left (snd f hL d V c (v ≫ k))
local notation "w" => Over.Hom.left (finiteKernelProjection f hL d V c k)

/-- Adjoining the freshly recomputed coefficients retains an already effective old kernel. -/
theorem nestedFiniteProjection_isPullback
    (H : IsPullback p q (v.left ≫ w) (v.left ≫ w)) :
    IsPullback p q (nestedFiniteProjection f hL d V c k v)
      (nestedFiniteProjection f hL d V c k v) := by
  apply IsKernelPair.cancel_right (f₂ := nestedFiniteToOld f hL d V c k v)
    (nestedFiniteProjection_condition f hL d V c k v)
  simpa only [nestedFiniteProjection_toOld] using H

variable {Z : Scheme} (a : Z ⟶ A.left)
  [Mono (a ≫ (finiteKernelProjection f hL d V c k).left)]

/-- Original seed-arrow division proves effectivity for BOTH retained coefficient systems. -/
theorem nestedFiniteProjection_isPullback_of_seed
    (t : B.left ⟶ pullback (snd f hL d V c k).left a)
    (ht : t ≫ SchemeRelationEtaleBranchPropagation.branch
      (fst f hL d V c k).left (snd f hL d V c k).left a = v.left) :
    IsPullback p q (nestedFiniteProjection f hL d V c k v)
      (nestedFiniteProjection f hL d V c k v) :=
  nestedFiniteProjection_isPullback f hL d V c k v
    (monicSeedSelection_isPullback f hL d V c k w
      (congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)) a v t ht)

end FLT.Mazur.HilbertChart.AffineRestriction
