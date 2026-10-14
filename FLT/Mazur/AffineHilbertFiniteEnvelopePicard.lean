/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteEnvelopeKernel

/-!
# Finite original equations detect Picard classes on full envelopes

The reconstructed finite-model kernel proves that the finitely many original
invariant coefficients detect equality in the original Picard fppf sheaf.
Tests may be nonaffine and nonreduced. This is a theorem about all maps from
a test to the selected original source, not global representability of the sheaf.
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
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  [IsIso (toEnvelope f hL d V c k).left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
local notation "σ" => sectionAt f hL d V c k

/-- The actual finite model detects precisely the original Picard section on every scheme test. -/
theorem finiteEnvelope_picard_test_iff {T : Over (Spec (.of R))} (a b : T ⟶ A) :
    a ≫ v = b ≫ v ↔
      (relativeFppfSheaf f).obj.map a.op σ = (relativeFppfSheaf f).obj.map b.op σ := by
  constructor
  · intro hab
    let H := finiteEnvelope_relative_isPullback f hL d V c k
    have hc := equal_class_natural f hL d V c k (H.lift a b hab)
    simpa only [IsPullback.lift_fst, IsPullback.lift_snd] using hc
  · intro hab
    obtain ⟨z, hz, _⟩ := lift f hL d V c k a b hab
    rw [← hz.1, ← hz.2, Category.assoc, Category.assoc,
      finiteKernelProjection_condition]

/-- A finite list of original coefficient equalities is an exact Picard class equality test. -/
theorem finiteEnvelope_picard_coefficients_iff {T : Over (Spec (.of R))} (a b : T ⟶ A) :
    (relativeFppfSheaf f).obj.map a.op σ = (relativeFppfSheaf f).obj.map b.op σ ↔
      ∀ s ∈ finiteKernelCoefficients f hL d V c k,
        a.left.appTop s.val = b.left.appTop s.val := by
  rw [← finiteEnvelope_picard_test_iff, finiteKernelProjection_test_iff,
    finiteKernelCoefficients_test]

/-- Solving the finite equations constructs a unique ORIGINAL Picard arrow on the whole test. -/
theorem finiteEnvelope_coefficients_lift {T : Over (Spec (.of R))} (a b : T ⟶ A)
    (hab : ∀ s ∈ finiteKernelCoefficients f hL d V c k,
      a.left.appTop s.val = b.left.appTop s.val) :
    ∃! z : T ⟶ relation f hL d V c k, z ≫ p = a ∧ z ≫ q = b :=
  lift f hL d V c k a b ((finiteEnvelope_picard_coefficients_iff f hL d V c k a b).mpr hab)

end FLT.Mazur.HilbertChart.AffineRestriction
