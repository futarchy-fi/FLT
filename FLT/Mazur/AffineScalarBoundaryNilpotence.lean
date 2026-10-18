/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Nilpotence on the actual original scalar boundary product

Construct the fiber product of two unchanged scalar spectra. A coordinate is
nilpotent there exactly when it vanishes at every pair of primes with the same
original scalar contraction. The product retains its full nonreduced structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)

/-- The full original scalar boundary product, with no reduction or quotient of its support. -/
def boundaryProduct : Scheme :=
  pullback (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom κ))

/-- Its first projection retains the original invariant-coordinate point. -/
def boundaryProjection : boundaryProduct s κ ⟶ Spec (.of B) :=
  pullback.fst _ _

instance boundaryProduct_isAffine : IsAffine (boundaryProduct s κ) := by
  unfold boundaryProduct
  infer_instance

/-- Pull back a coordinate to an actual global function on the full boundary product. -/
def boundaryCoordinate (b : B) : Γ(boundaryProduct s κ, ⊤) :=
  (boundaryProjection s κ).appTop ((Scheme.ΓSpecIso (.of B)).inv b)

/-- The coordinate's nonvanishing set is the original principal open pulled to the product. -/
theorem boundaryCoordinate_basicOpen (b : B) :
    (boundaryProduct s κ).basicOpen (boundaryCoordinate s κ b) =
      boundaryProjection s κ ⁻¹ᵁ PrimeSpectrum.basicOpen b := by
  rw [boundaryCoordinate, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]

/-- Nilpotence detects all original boundary scalar fibers simultaneously. -/
theorem boundaryCoordinate_nilpotent_iff (b : B) :
    IsNilpotent (boundaryCoordinate s κ b) ↔
      ∀ (Q : PrimeSpectrum B) (P : PrimeSpectrum T),
        PrimeSpectrum.comap s Q = PrimeSpectrum.comap κ P → b ∈ Q.asIdeal := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot, boundaryCoordinate_basicOpen]
  constructor
  · intro h Q P hc
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Spec.map (CommRingCat.ofHom s)) (g := Spec.map (CommRingCat.ofHom κ)) Q P hc
    by_contra hb
    have hm : z ∈ boundaryProjection s κ ⁻¹ᵁ PrimeSpectrum.basicOpen b := by
      change b ∉ (boundaryProjection s κ z).asIdeal
      change boundaryProjection s κ z = Q at hz
      rwa [hz]
    rw [h] at hm
    exact hm
  · intro h
    apply eq_bot_iff.mpr
    intro z hz
    exact hz (h (boundaryProjection s κ z) (pullback.snd (Spec.map (CommRingCat.ofHom s))
      (Spec.map (CommRingCat.ofHom κ)) z)
      (congrArg (fun f ↦ f z) (pullback.condition
        (f := Spec.map (CommRingCat.ofHom s)) (g := Spec.map (CommRingCat.ofHom κ)))))

/-- Failure constructs actual original prime pairs with a nonvanishing coordinate. -/
theorem boundaryCoordinate_not_nilpotent_iff (b : B) :
    ¬ IsNilpotent (boundaryCoordinate s κ b) ↔
      ∃ (Q : PrimeSpectrum B) (P : PrimeSpectrum T),
        PrimeSpectrum.comap s Q = PrimeSpectrum.comap κ P ∧ b ∉ Q.asIdeal := by
  rw [boundaryCoordinate_nilpotent_iff]
  push Not
  rfl

end FLT.Mazur.AffineScalarBoundaryNilpotence
