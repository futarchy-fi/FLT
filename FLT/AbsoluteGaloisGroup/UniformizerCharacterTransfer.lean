/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UniformizerCharacterPowers

/-!
# Uniformizer characters under an integral embedding

The image of a source uniformizer has a definite valuation in the target DVR.
Its inertia ratio proves the corresponding power relation between the two
characters. Equivariance is needed only on that uniformizer.
-/

@[expose] public noncomputable section
open IsLocalRing IsDiscreteValuationRing
namespace ThreeAdicPlan
variable {R S G H : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Group G] [MulSemiringAction G R] [Group H] [MulSemiringAction H S]
  (f : R →+* S) [IsLocalHom f] (hf : Function.Injective f)
  {π : R} (hπ : Irreducible π) {ϖ : S} (hϖ : Irreducible ϖ)

include hf

/-- The valuation of the embedded uniformizer determines the character transfer exponent. -/
theorem uniformizerCharacter_transfer :
    ∃ e : ℕ, addVal S (f π) = e ∧
      ∀ (g : (IsLocalRing.maximalIdeal R).inertia G) (h : (IsLocalRing.maximalIdeal S).inertia H),
        f (g.val • π) = h.val • f π →
        ResidueField.map f (uniformizerCharacter hπ g : ResidueField R) =
          (uniformizerCharacter hϖ h : ResidueField S) ^ e := by
  have hx : f π ≠ 0 := (map_ne_zero_iff f hf).mpr hπ.ne_zero
  obtain ⟨e, he, hr⟩ := exists_uniformizer_power_ratio (G := H) hϖ hx
  refine ⟨e, he, fun g h hgh ↦ ?_⟩
  obtain ⟨z, hz, hres⟩ := hr h
  have heq : f (uniformizerRatio hπ g.val : R) = z := by
    apply mul_right_cancel₀ hx
    calc
      f (uniformizerRatio hπ g.val : R) * f π = f (g.val • π) := by
        rw [← map_mul, mul_comm, uniformizer_mul_ratio]
      _ = z * f π := hgh.trans hz
  change residue S (f (uniformizerRatio hπ g.val : R)) = _
  rw [heq]
  exact hres

end ThreeAdicPlan
