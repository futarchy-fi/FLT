/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicNormalizedAtlas
public import FLT.Mazur.CyclicHomNormalizedRelabelModuli
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedRelabelModuli

/-!
# The two normalized charts cover the original smooth modular objects

Their actual natural modular maps preserve original classes under
normalization and relabeling, including arbitrary cyclic collisions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual normalized characteristic charts map naturally to the modular presheaf. -/
def normalizedModuliMap : (b : Bool) →
    yoneda.obj (normalizedLocus n b) ⋙ uliftFunctor.{1} ⟶ ampleCyclicClassPresheaf n
  | false => UniversalWeierstrass.cyclicHomNormalizedModuliMap n
  | true => OddWeierstrassParameter.cyclicHomNormalizedModuliMap n

/-- Both chart normalizations preserve the full original modular object on every source. -/
theorem normalizedModuliMap_normalization (b : Bool) {T : Scheme} (q : T ⟶ locus n b) :
    (normalizedModuliMap n b).app (Opposite.op T) (ULift.up (q ≫ normalization n b)) =
      ampleCyclicClassesPullback q n (moduliClass n b) := by
  cases b
  · exact (UniversalWeierstrass.cyclicHomNormalizedModuliMap_locusNormalization n q).trans
      (UniversalWeierstrass.cyclicHomLocusModuliClass_eq_pullback n q)
  · exact (OddWeierstrassParameter.cyclicHomNormalizedModuliMap_locusNormalization n q).trans
      (OddWeierstrassParameter.cyclicHomLocusModuliClass_eq_pullback n q)

/-- The common finite action retains every normalized test's original modular class. -/
theorem normalizedModuliMap_action (b : Bool) {T : Scheme}
    (q : T ⟶ normalizedLocus n b) (e : RelabelGroup n) :
    (normalizedModuliMap n b).app (Opposite.op T)
        (ULift.up (q ≫ (normalizedRelabelAction n b e).hom)) =
      (normalizedModuliMap n b).app (Opposite.op T) (ULift.up q) := by
  cases b
  · exact UniversalWeierstrass.cyclicHomNormalizedModuliMap_action n q e.1 e.2.2
  · exact OddWeierstrassParameter.cyclicHomNormalizedModuliMap_action n q e.2.1 e.2.2

/-- The actual closed normalized charts cover all original smooth ample cyclic families. -/
theorem exists_normalized_moduli_fppf_cover {S : Scheme} {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, (normalizedModuliMap n (b i)).app (Opposite.op (C.X i)) (ULift.up (q i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, b, q, hq⟩ := exists_moduli_fppf_cover n H hc ha
  exact ⟨C, b, fun i ↦ q i ≫ normalization n (b i),
    fun i ↦ (normalizedModuliMap_normalization n (b i) (q i)).trans (hq i)⟩

end FLT.Mazur.CyclicCharacteristicAtlas
