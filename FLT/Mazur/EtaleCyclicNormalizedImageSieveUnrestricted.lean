/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicOriginalNormalizedCoverageUnrestricted
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import FLT.Mazur.NormalizedModuliDescentUniversal

/-!
# Unrestricted fppf image coverage for actual original modular classes

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
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- The full normalized chart's image sieve covers the actual original class. -/
theorem normalized_imageSieve_mem_unrestricted :
    Presheaf.imageSieve (cyclicNormalizedSliceModuliMap n)
      (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) ∈ Scheme.fppfTopology S := by
  obtain ⟨C, p, hp⟩ := exists_normalized_fppf_cover_unrestricted H hc ha h₂ hn
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨ULift.up (p i), hp i⟩

include h₂ hn in
/-- Coverage survives every base change, even to a nonnoetherian test scheme. -/
theorem normalized_pullback_imageSieve_mem_unrestricted {T : Scheme} (g : T ⟶ S) :
    Presheaf.imageSieve (cyclicNormalizedSliceModuliMap n)
      (ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) ∈
        Scheme.fppfTopology T := by
  have h := Scheme.fppfTopology.pullback_stable g (normalized_imageSieve_mem_unrestricted H hc ha
    h₂ hn)
  rwa [Presheaf.pullback_imageSieve] at h

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-!
# Unrestricted invariants evaluated on actual original smooth etale cyclic objects

The atlas is constructed from the original object. A map from the normalized
slice invariant under the unmarked modular relation therefore gives a unique
map from the original base, with the correct value on every test parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- Unmarked modular invariants evaluate uniquely on each original smooth etale object. -/
theorem exists_unique_original_invariant_unrestricted {Y : Scheme} (v : cyclicNormalizedSlice n ⟶ Y)
    (hv : CyclicModuliInvariant n v) :
    ∃! d : S ⟶ Y, ∀ (T : Scheme) (g : T ⟶ S) (q : T ⟶ cyclicNormalizedSlice n),
      (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up q) =
        ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) →
          g ≫ d = q ≫ v := by
  obtain ⟨C, p, hp⟩ := exists_normalized_fppf_cover_unrestricted H hc ha h₂ hn
  exact cyclicModuliInvariant_unique_evaluation n v hv _ C p hp

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
