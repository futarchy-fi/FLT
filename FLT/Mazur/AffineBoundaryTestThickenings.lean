/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryTestIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Infinitesimal neighborhoods defined by the original boundary tests

Positive powers of the actual finite test ideal define closed subschemes of
the full scalar boundary product. Their common support is computed directly
from the original tests. The schemes retain their ideal-power structures.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)

/-- The actual original test ideal, regarded as an ideal sheaf on the full product. -/
def boundaryTestSheaf : (boundaryProduct s κ).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (boundaryTestIdeal s κ a)

/-- Retain each positive ideal power, rather than passing to a reduced closed subset. -/
def boundaryTestThickening (k : ℕ) : Scheme :=
  (boundaryTestSheaf s κ a ^ (k + 1)).subscheme

/-- The actual closed immersion into the unchanged original scalar product. -/
def boundaryTestThickeningMap (k : ℕ) :
    boundaryTestThickening s κ a k ⟶ boundaryProduct s κ :=
  (boundaryTestSheaf s κ a ^ (k + 1)).subschemeι

instance (k : ℕ) : IsClosedImmersion (boundaryTestThickeningMap s κ a k) := by
  unfold boundaryTestThickeningMap
  infer_instance

/-- A point of any order lies over exactly a simultaneous zero of the original tests. -/
theorem mem_boundaryTestThickening_range (k : ℕ) (z : boundaryProduct s κ) :
    z ∈ Set.range (boundaryTestThickeningMap s κ a k) ↔
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal := by
  change z ∈ Set.range (boundaryTestSheaf s κ a ^ (k + 1)).subschemeι ↔ _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow_succ]
  change z ∈ (Scheme.IdealSheafData.ofIdealTop (boundaryTestIdeal s κ a)).support ↔ _
  change z ∈ (boundaryProduct s κ).zeroLocus (U := ⊤)
    (boundaryTestIdeal s κ a : Set _) ↔ _
  rw [boundaryTestIdeal, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h t ht
    have hn := h _ ⟨t, ht, rfl⟩
    rw [boundaryCoordinate_basicOpen] at hn
    exact not_not.mp hn
  · rintro h _ ⟨t, ht, rfl⟩
    rw [boundaryCoordinate_basicOpen]
    exact fun hn ↦ hn (h t ht)

/-- Every stage carries the exact kernel ideal power of the original test sheaf. -/
theorem boundaryTestThickeningMap_kernel (k : ℕ) :
    (boundaryTestThickeningMap s κ a k).ker = boundaryTestSheaf s κ a ^ (k + 1) :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- Surjectivity of any order is equivalent to nilpotence in the full unreduced product. -/
theorem boundaryTestThickeningMap_surjective_iff (k : ℕ) :
    Function.Surjective (boundaryTestThickeningMap s κ a k) ↔
      IsNilpotent (boundaryTestIdeal s κ a) := by
  rw [boundaryTestIdeal_nilpotent_iff]
  constructor
  · intro h t ht
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot, boundaryCoordinate_basicOpen]
    apply eq_bot_iff.mpr
    intro z hz
    exact hz ((mem_boundaryTestThickening_range s κ a k z).mp (h z) t ht)
  · intro h z
    apply (mem_boundaryTestThickening_range s κ a k z).mpr
    intro t ht
    have he := (Scheme.isNilpotent_iff_basicOpen_eq_bot _).mp (h t ht)
    rw [boundaryCoordinate_basicOpen] at he
    by_contra hn
    have hm : z ∈ boundaryProjection s κ ⁻¹ᵁ PrimeSpectrum.basicOpen t := hn
    rw [he] at hm
    exact hm

end FLT.Mazur.AffineScalarBoundaryNilpotence
