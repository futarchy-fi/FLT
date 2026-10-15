/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteKernelModel

/-!
# Invariant principal sources are saturated under the entire finite kernel

The finite equations detect the full invariant spectrum on arbitrary scheme
tests, even before a ground map on the test is specified. Consequently an
original invariant principal open contains one endpoint of a finite-kernel
point exactly when it contains the other. This uses the old finite model,
without assuming that its kernel is already the original Picard relation.
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
local notation "v" => finiteKernelProjection f hL d V c k
local notation "i" => invariantAffineProjection f hL d V c k

/-- Equality of finite coefficients detects full invariants on any scheme test. -/
theorem finiteKernel_scheme_test_iff {T : Scheme} (a b : T ⟶ A.left) :
    a ≫ (v).left = b ≫ (v).left ↔ a ≫ (i).left = b ≫ (i).left := by
  constructor
  · intro h
    have hb : b ≫ A.hom = a ≫ A.hom := by
      have hh := congrArg (fun t ↦ t ≫ (finiteKernelModel f hL d V c k).hom) h
      simpa only [Category.assoc, (v).w] using hh.symm
    let a' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk a rfl
    let b' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk b hb
    exact congrArg Over.Hom.left
      ((finiteKernelProjection_test_iff f hL d V c k a' b').mp (Over.OverMorphism.ext h))
  · intro h
    have hb : b ≫ A.hom = a ≫ A.hom := by
      have hh := congrArg (fun t ↦ t ≫ (invariantAffineModel f hL d V c k).hom) h
      simpa only [Category.assoc, (i).w] using hh.symm
    let a' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk a rfl
    let b' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk b hb
    exact congrArg Over.Hom.left
      ((finiteKernelProjection_test_iff f hL d V c k a' b').mpr (Over.OverMorphism.ext h))

local notation "x" => pullback.fst (Over.Hom.left v) (Over.Hom.left v)
local notation "y" => pullback.snd (Over.Hom.left v) (Over.Hom.left v)

/-- The whole old finite kernel preserves every original invariant principal source open. -/
theorem finiteKernel_invariant_preimage
    (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left) :
    x ⁻¹ᵁ A.left.basicOpen s.val = y ⁻¹ᵁ A.left.basicOpen s.val := by
  have h := (finiteKernel_scheme_test_iff f hL d V c k x y).mp pullback.condition
  have hh := congrArg (fun t ↦ t ⁻¹ᵁ PrimeSpectrum.basicOpen s) h
  simp only [Scheme.Hom.comp_preimage, invariantAffineProjection, Over.homMk_left] at hh
  have he := SchemeRelationInvariantSpectrum.projection_preimage_basicOpen
    (fst f hL d V c k).left (snd f hL d V c k).left s
  rw [he] at hh
  exact hh

/-- No residue-field branch can leave an invariant principal source while keeping coefficients. -/
theorem finiteKernel_principal_mem_iff
    (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
    (z : (pullback (v).left (v).left : Scheme)) :
    x z ∈ A.left.basicOpen s.val ↔ y z ∈ A.left.basicOpen s.val :=
  SetLike.ext_iff.mp (finiteKernel_invariant_preimage f hL d V c k s) z

end FLT.Mazur.HilbertChart.AffineRestriction
