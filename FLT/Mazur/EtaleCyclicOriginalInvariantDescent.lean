/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicNormalizedFppfCover
public import FLT.Mazur.NormalizedModuliDescentUniversal

/-!
# Invariants evaluated on actual original smooth etale cyclic objects

The atlas is constructed from the original object. A map from the normalized
slice invariant under the unmarked modular relation therefore gives a unique
map from the original base, with the correct value on every test parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- Unmarked modular invariants evaluate uniquely on each original smooth etale object. -/
theorem exists_unique_original_invariant {Y : Scheme} (v : cyclicNormalizedSlice n ⟶ Y)
    (hv : CyclicModuliInvariant n v) :
    ∃! d : S ⟶ Y, ∀ (T : Scheme) (g : T ⟶ S) (q : T ⟶ cyclicNormalizedSlice n),
      (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up q) =
        ampleCyclicClassesPullback g n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) →
          g ≫ d = q ≫ v := by
  obtain ⟨C, p, hp⟩ := exists_normalized_fppf_cover H hc ha h₂ hn
  exact cyclicModuliInvariant_unique_evaluation n v hv _ C p hp

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
