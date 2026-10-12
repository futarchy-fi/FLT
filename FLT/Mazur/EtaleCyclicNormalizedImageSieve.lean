/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicNormalizedFppfCover
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Fppf image coverage for actual original modular classes

The sieve of maps on which the original class has a full normalized parameter
is covering. Pulling this sieve back gives coverage over arbitrary test schemes,
without requiring those test schemes to be locally noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- The full normalized chart's image sieve covers the actual original class. -/
theorem normalized_imageSieve_mem :
    Presheaf.imageSieve (cyclicNormalizedSliceModuliMap n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) ∈ Scheme.fppfTopology S := by
  obtain ⟨C, p, hp⟩ := exists_normalized_fppf_cover H hc ha h₂ hn
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨ULift.up (p i), hp i⟩

include h₂ hn in
/-- Coverage survives every base change, even to a nonnoetherian test scheme. -/
theorem normalized_pullback_imageSieve_mem {T : Scheme} (g : T ⟶ S) :
    Presheaf.imageSieve (cyclicNormalizedSliceModuliMap n)
      (ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) ∈
        Scheme.fppfTopology T := by
  have h := Scheme.fppfTopology.pullback_stable g (normalized_imageSieve_mem H hc ha h₂ hn)
  rwa [Presheaf.pullback_imageSieve] at h

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
