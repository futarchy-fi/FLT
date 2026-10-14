/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteKernelModel
public import FLT.Mazur.AffineHilbertEnvelopeQuotient

/-!
# Full-envelope certificates for the original finite coefficient kernel

The original finite equations detect every affine invariant morphism. Applied
to the constructed full-envelope quotient, this proves that the original
Picard relation is the entire finite-model kernel. No seed certificate,
source orbit coverage, or identification of a target with its image is input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k

/-- Finite original invariant equations detect every invariant map to an affine scheme. -/
theorem finiteKernel_eq_affine_invariant {Y : Scheme} [IsAffine Y]
    (g : A.left ⟶ Y) (hg : (p).left ≫ g = (q).left ≫ g)
    {T : Over (Spec (.of R))} (a b : T ⟶ A) (hab : a ≫ v = b ≫ v) :
    a.left ≫ g = b.left ≫ g := by
  have hi := congrArg Over.Hom.left
    ((finiteKernelProjection_test_iff f hL d V c k a b).mp hab)
  change a.left ≫ SchemeRelationInvariantSpectrum.projection (p).left (q).left =
    b.left ≫ SchemeRelationInvariantSpectrum.projection (p).left (q).left at hi
  rw [← SchemeRelationInvariantSpectrum.projection_descend (p).left (q).left g hg]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ SchemeRelationInvariantSpectrum.descend (p).left (q).left g hg) hi

variable [IsAffine V.left] [IsIso (toEnvelope f hL d V c k).left]
local notation "g" => fullEnvelopeRelativeProjection f hL d V c k

/-- Equality in the finite model constructs equality in the actual full-envelope quotient. -/
theorem finiteKernel_eq_fullEnvelope {T : Over (Spec (.of R))} (a b : T ⟶ A)
    (hab : a ≫ v = b ≫ v) : a ≫ g = b ≫ g := by
  apply Over.OverMorphism.ext
  exact finiteKernel_eq_affine_invariant f hL d V c k (g).left
    (fullEnvelopeProjection_equalizes f hL d V c k) a b hab

/-- The full original relation is the finite model's relative kernel, proved from reconstruction. -/
theorem finiteEnvelope_relative_isPullback : IsPullback p q v v := by
  let H := fullEnvelope_relative_kernelPair f hL d V c k
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (finiteKernelProjection_condition f hL d V c k)
    (fun t ↦ H.lift t.fst t.snd
      (finiteKernel_eq_fullEnvelope f hL d V c k t.fst t.snd t.condition))
    (fun _ ↦ H.lift_fst _ _ _) (fun _ ↦ H.lift_snd _ _ _) ?_)
  intro t b hb₁ hb₂
  apply hom_ext f hL d V c k
  · exact hb₁.trans (H.lift_fst _ _ _).symm
  · exact hb₂.trans (H.lift_snd _ _ _).symm

/-- Forgetting the base retains the complete scheme kernel, including nilpotent directions. -/
theorem finiteEnvelope_isPullback :
    IsPullback (p).left (q).left (v).left (v).left :=
  (finiteEnvelope_relative_isPullback f hL d V c k).map (Over.forget _)

end FLT.Mazur.HilbertChart.AffineRestriction
