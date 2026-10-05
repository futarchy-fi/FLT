/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.RationalPDDescent

/-!
# Enlarging an integral PD ideal by a base PD ideal

Inside a rational algebra, factorial cancellation proves compatibility of
all existing divided powers. Their sum therefore inherits integral divided
powers, with both original maps proved to be PD morphisms.
-/

@[expose] public noncomputable section
namespace DividedPowers
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra ℚ B]
  (f : A →+* B) (I : Ideal A) (hI : DividedPowers I)
  (g : R →+* A) (J : Ideal R) (hJ : DividedPowers J)

/-- Every ring map into a rational algebra preserves the factorial value of divided powers. -/
theorem map_dpow_rational (n : ℕ) {x : A} (hx : x ∈ I) :
    f (hI.dpow n x) = (rationalDpow (B := B)).dpow n (f x) := by
  apply (IsUnit.natCast_factorial_of_algebra ℚ n).mul_left_cancel
  calc
    (n.factorial : B) * f (hI.dpow n x) = f x ^ n := by
      simpa only [map_mul, map_natCast, map_pow] using congrArg f
        (hI.factorial_mul_dpow_eq_pow (n := n) hx)
    _ = _ := ((rationalDpow (B := B)).factorial_mul_dpow_eq_pow
      (Submodule.mem_top : f x ∈ (⊤ : Ideal B))).symm

include hI hJ in
/-- Generators of the sum lift all their positive rational divided powers into that sum. -/
theorem rationalPDSum_generator (n : ℕ) (hn : n ≠ 0)
    (x : A) (hx : x ∈ (I : Set A) ∪ g '' (J : Set R)) :
    ∃ y ∈ I ⊔ J.map g, f y = (rationalDpow (B := B)).dpow n (f x) := by
  rcases hx with hx | ⟨z, hz, rfl⟩
  · exact ⟨hI.dpow n x, (show I ≤ I ⊔ J.map g from le_sup_left) (hI.dpow_mem hn hx),
      map_dpow_rational f I hI n hx⟩
  · exact ⟨g (hJ.dpow n z), (show J.map g ≤ I ⊔ J.map g from le_sup_right)
        (Ideal.mem_map_of_mem g (hJ.dpow_mem hn hz)),
      map_dpow_rational (f.comp g) J hJ n hz⟩

/-- The enlarged ideal carries actual integral divided powers. -/
def rationalPDSum (hf : Function.Injective f) : DividedPowers (I ⊔ J.map g) :=
  rationalDividedPowers f (I ⊔ J.map g) hf
    (by rw [Ideal.span_union, Ideal.span_eq, Ideal.map])
    (rationalPDSum_generator f I hI g J hJ)

/-- Enlarging the ideal preserves the old operations on their original domain. -/
theorem rationalPDSum_restrict (hf : Function.Injective f) (n : ℕ)
    {x : A} (hx : x ∈ I) :
    (rationalPDSum f I hI g J hJ hf).dpow n x = hI.dpow n x := by
  apply hf
  exact (rationalDividedPowers_map f _ hf _ _ n ((show I ≤ I ⊔ J.map g from le_sup_left) hx)).trans
    (map_dpow_rational f I hI n hx).symm

/-- The enlarged operations agree with the base PD structure under the original map. -/
theorem rationalPDSum_base (hf : Function.Injective f) (n : ℕ)
    {x : R} (hx : x ∈ J) :
    (rationalPDSum f I hI g J hJ hf).dpow n (g x) = g (hJ.dpow n x) := by
  apply hf
  exact (rationalDividedPowers_map f _ hf _ _ n
    ((show J.map g ≤ I ⊔ J.map g from le_sup_right) (Ideal.mem_map_of_mem g hx))).trans
      (map_dpow_rational (f.comp g) J hJ n hx).symm

/-- The old ideal's inclusion into the enlarged PD ring is a PD morphism. -/
theorem rationalPDSum_inclusion (hf : Function.Injective f) :
    hI.IsDPMorphism (rationalPDSum f I hI g J hJ hf) (RingHom.id A) := by
  refine ⟨?_, fun x hx ↦ rationalPDSum_restrict f I hI g J hJ hf _ hx⟩
  simp

/-- The original base map is a PD morphism into the enlarged ideal. -/
theorem rationalPDSum_isDPMorphism (hf : Function.Injective f) :
    hJ.IsDPMorphism (rationalPDSum f I hI g J hJ hf) g :=
  ⟨le_sup_right, fun _ hx ↦ rationalPDSum_base f I hI g J hJ hf _ hx⟩

end DividedPowers
