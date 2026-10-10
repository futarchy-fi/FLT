/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisDeterminant
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The actual determinant open for a proposed basis

The principal open of the coordinate determinant is exactly the locus where
the vectors form a basis after localization. It commutes with arbitrary scalar
extension and has the expected affine localization factorization property.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] {d : ℕ}
variable (b : Module.Basis (Fin d) S A) (y : Fin d → A)

/-- The actual principal open defined by the coordinate determinant. -/
def basisOpen : TopologicalSpace.Opens (PrimeSpectrum S) :=
  PrimeSpectrum.basicOpen (basisDeterminant b y)

/-- A prime lies in the determinant open exactly when the localized vectors form a basis. -/
theorem mem_basisOpen_iff (p : PrimeSpectrum S) :
    p ∈ basisOpen b y ↔
      ∃ c : Module.Basis (Fin d) (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[S] A),
        ∀ i, c i = baseChangedTuple y (Localization.AtPrime p.asIdeal) i := by
  rw [baseChange_exists_basis_iff b y,
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p.asIdeal) p.asIdeal]
  rfl

variable (T : Type*) [CommRing T] [Algebra S T]

/-- The actual basis open commutes with arbitrary scalar extension. -/
theorem basisOpen_baseChange :
    basisOpen (A := T ⊗[S] A) (b.baseChange T) (baseChangedTuple y T) =
      TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap (algebraMap S T), PrimeSpectrum.continuous_comap _⟩
        (basisOpen b y) := by
  rw [basisOpen, basisDeterminant_baseChange]
  rfl

/-- An affine test map factors through the localization exactly when the tuple becomes a basis. -/
theorem basisOpen_factorization_iff :
    Nonempty (Localization.Away (basisDeterminant b y) →ₐ[S] T) ↔
      ∃ c : Module.Basis (Fin d) T (T ⊗[S] A), ∀ i, c i = baseChangedTuple y T i := by
  rw [baseChange_exists_basis_iff b y]
  constructor
  · rintro ⟨f⟩
    have h := (IsLocalization.Away.algebraMap_isUnit (basisDeterminant b y)
      (S := Localization.Away (basisDeterminant b y))).map f
    simpa only [AlgHom.commutes] using h
  · intro h
    exact ⟨IsLocalization.Away.liftAlgHom (basisDeterminant b y)
      (f := Algebra.ofId S T) h⟩

end FLT.Mazur.HilbertChart
