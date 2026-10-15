/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChange
public import FLT.Mazur.PrincipalOpenTensorRange

/-!
# The two original boundary opens are disjoint on the special fiber

The original tensor incidence relation t * u = π separates the two opens
whenever the coefficient map kills π, independently of normalization or depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (hπ : algebraMap R S π = 0)
local notation "t" => coord W s π b3 b4 b6 0
local notation "v" => coord W s π b3 b4 b6 2
local notation "T" => ScalarExtension W s π b3 b4 b6 S

include hπ in
/-- No prime of the original tensor algebra avoids both boundary functions. -/
theorem tensorBoundary_not_both (z : PrimeSpectrum T) :
    ¬ (tensorCoord W s π b3 b4 b6 S 0 ∉ z.asIdeal ∧
      tensorCoord W s π b3 b4 b6 S 2 ∉ z.asIdeal) := by
  rintro ⟨ht, hu⟩
  have he : tensorCoord W s π b3 b4 b6 S 0 * tensorCoord W s π b3 b4 b6 S 2 = 0 := by
    rw [baseChange_incidence, hπ, map_zero]
  have hm := z.isPrime.mem_or_mem (he ▸ z.asIdeal.zero_mem)
  exact hm.elim ht hu

include hπ in
/-- The full principal tensor boundaries have disjoint geometric images. -/
theorem tensorBoundary_disjoint :
    Disjoint (Set.range (PrincipalOpenTensor.inclusion (R := R) S t))
      (Set.range (PrincipalOpenTensor.inclusion (R := R) S v)) := by
  rw [PrincipalOpenTensor.inclusion_range, PrincipalOpenTensor.inclusion_range]
  apply Set.disjoint_left.mpr
  intro z ht hu
  exact tensorBoundary_not_both W s π b3 b4 b6 S hπ z ⟨ht, hu⟩

end FLT.Mazur.WeierstrassSuccessiveX
