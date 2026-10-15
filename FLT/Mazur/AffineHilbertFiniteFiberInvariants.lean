/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteInvariantOpens
public import FLT.Mazur.AffineHilbertInvariantEnvelope

/-!
# Invariant coefficients detect entire original finite-model fibers

Two source points above the same finite coefficient point have a point in
their scheme pullback, even when their residue fields differ. Saturation of
that full kernel therefore propagates every invariant principal neighborhood
between them. No original Picard arrow or split residue-field branch is assumed.
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
local notation "C" => compatibleFunctions
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k))

/-- A single invariant principal source contains either all or none of a finite-model fiber. -/
theorem finiteFiber_principal_mem_iff (s : C) (x y : A.left) (hxy : v x = v y) :
    x ∈ A.left.basicOpen s.val ↔ y ∈ A.left.basicOpen s.val := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback v v) x y hxy
  simpa only [hz₁, hz₂] using finiteKernel_principal_mem_iff f hL d V c k s z

/-- Any ideal of original invariant coefficients has fiberwise constant nonvanishing. -/
theorem finiteFiber_ideal_nonvanishing_iff (I : Ideal C) (x y : A.left)
    (hxy : v x = v y) :
    (∃ s ∈ I, x ∈ A.left.basicOpen s.val) ↔
      ∃ s ∈ I, y ∈ A.left.basicOpen s.val := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, (finiteFiber_principal_mem_iff f hL d V c k s x y hxy).mp hx⟩
  · rintro ⟨s, hs, hy⟩
    exact ⟨s, hs, (finiteFiber_principal_mem_iff f hL d V c k s x y hxy).mpr hy⟩

/-- One actual admissible coefficient propagates to every original source in the same fiber. -/
theorem finiteFiber_admissible_coverage (x : A.left) (s : C)
    (hs : s ∈ invariantEnvelopeDenominators f hL d V c k)
    (hx : x ∈ A.left.basicOpen s.val) :
    ∀ y : A.left, v y = v x →
      ∃ t : C, t ∈ invariantEnvelopeDenominators f hL d V c k ∧
        y ∈ A.left.basicOpen t.val := by
  intro y hy
  exact ⟨s, hs, (finiteFiber_principal_mem_iff f hL d V c k s x y hy.symm).mp hx⟩

end FLT.Mazur.HilbertChart.AffineRestriction
