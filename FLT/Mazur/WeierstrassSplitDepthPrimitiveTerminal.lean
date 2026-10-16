/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# The primitive terminal coefficient at odd split depth

At original depth 2k+1 the divided constant has exact depth one. Its quotient
by the uniformizer is therefore a unit, and this module constructs that unit
from the original coefficient conditions instead of assuming primitivity.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (2 * k + 1)) (d : Data W π k)

include D in
/-- Exact odd split depth constructs a primitive integral terminal constant. -/
theorem splitDepth_exists_primitive_terminal : ∃ u : Rˣ, d.b6 = π * ↑u := by
  have he := divided_constant_exact_depth D d (by omega)
  have hdepth : 2 * k + 1 - 2 * k = 1 := by omega
  rw [hdepth, pow_one] at he
  have hd : π ∣ d.b6 := by
    simpa only [D.maximalIdeal_eq, Ideal.mem_span_singleton] using he.1
  obtain ⟨c, hc⟩ := hd
  have hu : IsUnit c := by
    rw [← notMem_maximalIdeal]
    intro hm
    apply he.2
    rw [hc]
    have hp : π ∈ maximalIdeal R :=
      D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
    change π * c ∈ maximalIdeal R ^ 2
    rw [pow_two]
    exact Ideal.mul_mem_mul hp hm
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, by simpa only [hu] using hc⟩

/-- The integral unit determined by the original terminal constant. -/
def splitDepthPrimitiveTerminalUnit : Rˣ :=
  Classical.choose (splitDepth_exists_primitive_terminal D d)

/-- The constructed unit retains the entire original divided constant. -/
theorem splitDepthPrimitiveTerminalUnit_spec :
    d.b6 = π * ↑(splitDepthPrimitiveTerminalUnit D d) :=
  Classical.choose_spec (splitDepth_exists_primitive_terminal D d)

/-- The primitive factor is unique over the original domain. -/
theorem splitDepthPrimitiveTerminalUnit_unique (u : Rˣ) (hu : d.b6 = π * ↑u) :
    splitDepthPrimitiveTerminalUnit D d = u := by
  apply Units.ext
  exact mul_left_cancel₀ D.uniformizer_ne_zero
    ((splitDepthPrimitiveTerminalUnit_spec D d).symm.trans hu)

end FLT.Mazur.WeierstrassDividedDepth
