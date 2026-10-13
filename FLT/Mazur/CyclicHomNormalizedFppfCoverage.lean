/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomNormalizedModuli
public import FLT.Mazur.CyclicHomLocusFppfCoverage

/-!
# Normalized actual subgroup charts cover original modular classes

The existing original fppf cover factors through the actual normalized
subgroup locus. The resulting modular class is the original pullback class,
with no etaleness or coprimality hypothesis on the cyclic subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (hc : H.IsCyclic) (ha : H.IsAmple) (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂ in
/-- The universal non-etale subgroup locus covers the actual original modular class. -/
theorem exists_hom_moduli_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomUniversalMultiplicationLocus n),
      ∀ i, (cyclicHomLocusModuliMap n).app (Opposite.op (C.X i)) (ULift.up (q i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, q, hq⟩ := H.exists_universal_hom_subgroup_fppf_cover hc h₂
  refine ⟨C, q, fun i ↦ ?_⟩
  change cyclicHomLocusModuliClass n (q i) = _
  rw [cyclicHomLocusModuliClass_eq_pullback]
  exact Quotient.sound (hq i)

include h₂ in
/-- The closed normalized non-etale locus covers each original smooth cyclic modular class. -/
theorem exists_hom_normalized_moduli_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomNormalizedLocus n),
      ∀ i, (cyclicHomNormalizedModuliMap n).app (Opposite.op (C.X i)) (ULift.up (q i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, p, q, J, hJ⟩ := H.exists_hom_locus_fppf_cover hc h₂
  have hz i := cyclicHomMultiplicationEquation_of_subgroup n (p i) (J i) (hJ i).2.1
  refine ⟨C, (fun i ↦ cyclicHomNormalizedLocusPoint n (p i) (hz i)), fun i ↦ ?_⟩
  rw [cyclicHomNormalizedModuliMap_normalization]
  obtain ⟨a⟩ := (hJ i).2.2.2
  exact Quotient.sound ⟨(compatibleIsoOfIdealEq _ (J i)
    ((cyclicHomSubgroup_ideal n (p i) (hz i)).trans (hJ i).2.1.symm)).trans a⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
