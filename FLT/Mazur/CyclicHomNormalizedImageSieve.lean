/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomNormalizedFppfCoverage
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Fppf image coverage for normalized non-etale subgroup parameters

The actual original modular class lies fppf locally in the normalized closed
subgroup chart. Its image sieve remains covering on every base change. The
original base still satisfies the stated local noetherian and two-unit hypotheses.
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
/-- The actual normalized non-etale chart's image sieve covers the original modular class. -/
theorem hom_normalized_imageSieve_mem :
    Presheaf.imageSieve (cyclicHomNormalizedModuliMap n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) ∈ Scheme.fppfTopology S := by
  obtain ⟨C, p, hp⟩ := H.exists_hom_normalized_moduli_fppf_cover hc ha h₂
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨ULift.up (p i), hp i⟩

include h₂ in
/-- Original coverage survives every base change, including nonnoetherian test schemes. -/
theorem hom_normalized_pullback_imageSieve_mem {T : Scheme} (g : T ⟶ S) :
    Presheaf.imageSieve (cyclicHomNormalizedModuliMap n)
      (ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) ∈
        Scheme.fppfTopology T := by
  have h := Scheme.fppfTopology.pullback_stable g (H.hom_normalized_imageSieve_mem hc ha h₂)
  rwa [Presheaf.pullback_imageSieve] at h

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
