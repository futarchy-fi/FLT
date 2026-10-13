/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomNormalizedModuli
public import FLT.Mazur.CyclicHomDivisorFppfCoverageUnrestricted
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Unrestricted normalized actual subgroup charts cover original modular classes

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
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (hc : H.IsCyclic) (ha : H.IsAmple) (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂ in
/-- The universal non-etale subgroup locus covers the actual original modular class. -/
theorem exists_hom_moduli_fppf_cover_unrestricted :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomUniversalMultiplicationLocus n),
      ∀ i, (cyclicHomLocusModuliMap n).app (Opposite.op (C.X i)) (ULift.up (q i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, q, hq⟩ := H.exists_universal_hom_subgroup_fppf_cover_unrestricted hc h₂
  refine ⟨C, q, fun i ↦ ?_⟩
  change cyclicHomLocusModuliClass n (q i) = _
  rw [cyclicHomLocusModuliClass_eq_pullback]
  exact Quotient.sound (hq i)

include h₂ in
/-- The closed normalized non-etale locus covers each original smooth cyclic modular class. -/
theorem exists_hom_normalized_moduli_fppf_cover_unrestricted :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomNormalizedLocus n),
      ∀ i, (cyclicHomNormalizedModuliMap n).app (Opposite.op (C.X i)) (ULift.up (q i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, p, q, J, hJ⟩ := H.exists_hom_locus_fppf_cover_unrestricted hc h₂
  have hz i := cyclicHomMultiplicationEquation_of_subgroup n (p i) (J i) (hJ i).2.1
  refine ⟨C, (fun i ↦ cyclicHomNormalizedLocusPoint n (p i) (hz i)), fun i ↦ ?_⟩
  rw [cyclicHomNormalizedModuliMap_normalization]
  obtain ⟨a⟩ := (hJ i).2.2.2
  exact Quotient.sound ⟨(compatibleIsoOfIdealEq _ (J i)
    ((cyclicHomSubgroup_ideal n (p i) (hz i)).trans (hJ i).2.1.symm)).trans a⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-!
# Unrestricted fppf image coverage for normalized non-etale subgroup parameters

The actual original modular class lies fppf locally in the normalized closed
subgroup chart. Its image sieve remains covering on every base change. The
original base is arbitrary, with two invertible.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (hc : H.IsCyclic) (ha : H.IsAmple) (h₂ : IsUnit (2 : Γ(S, ⊤)))

include h₂ in
/-- The actual normalized non-etale chart's image sieve covers the original modular class. -/
theorem hom_normalized_imageSieve_mem_unrestricted :
    Presheaf.imageSieve (cyclicHomNormalizedModuliMap n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) ∈ Scheme.fppfTopology S := by
  obtain ⟨C, p, hp⟩ := H.exists_hom_normalized_moduli_fppf_cover_unrestricted hc ha h₂
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨ULift.up (p i), hp i⟩

include h₂ in
/-- Original coverage survives every base change, including nonnoetherian test schemes. -/
theorem hom_normalized_pullback_imageSieve_mem_unrestricted {T : Scheme} (g : T ⟶ S) :
    Presheaf.imageSieve (cyclicHomNormalizedModuliMap n)
      (ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) ∈
        Scheme.fppfTopology T := by
  have h := Scheme.fppfTopology.pullback_stable g (H.hom_normalized_imageSieve_mem_unrestricted hc
    ha h₂)
  rwa [Presheaf.pullback_imageSieve] at h

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
