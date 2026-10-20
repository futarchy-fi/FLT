/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicNormalizedSubgroup
public import FLT.Mazur.CompatibleSubgroupSmooth

/-!
# The smooth scope of the original normalized parameter charts

Both normalized charts carry smooth whole curves. A genuine compatible
comparison therefore cannot identify a parameter with a nonsmooth boundary
family. Boundary coverage requires additional charts.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Both characteristic source curves are smooth on their entire parameter bases. -/
instance characteristicCurve_smooth (b : Bool) : Smooth (curve n b).curve.hom := by
  cases b
  · exact SmoothOfRelativeDimension.smooth 1
      (UniversalWeierstrass.cyclicHomSourceCurve n _).curve.hom
  · exact SmoothOfRelativeDimension.smooth 1
      (OddWeierstrassParameter.cyclicHomSourceCurve n _).curve.hom

/-- Restriction to the normalized slices retains smoothness of the whole curve. -/
instance normalizedCurve_smooth (b : Bool) : Smooth (normalizedCurve n b).curve.hom :=
  inferInstanceAs (Smooth (pullback.snd (curve n b).curve.hom (normalizedInclusion n b)))

/-- Every actual normalized parameter has a smooth whole curve over its test scheme. -/
instance normalizedCurve_baseChange_smooth {T : Scheme} (b : Bool)
    (q : T ⟶ normalizedLocus n b) : Smooth ((normalizedCurve n b).baseChange q).curve.hom :=
  inferInstanceAs (Smooth (pullback.snd (normalizedCurve n b).curve.hom q))

/-- A full compatible normalized presentation forces the original whole curve to be smooth. -/
theorem smooth_of_normalized_comparison {S : Scheme} {E : GeneralizedEllipticCurve S}
    (H : E.FiniteSubgroup n) (b : Bool) (q : S ⟶ normalizedLocus n b)
    (h : Nonempty (CompatibleIso ((normalizedSubgroup n b).baseChange q) H)) :
    Smooth E.curve.hom := by
  obtain ⟨a⟩ := h
  exact a.smooth_iff.mp inferInstance

/-- Equality of actual modular classes also forces smoothness, not just pointwise resemblance. -/
theorem smooth_of_normalized_moduli_eq {S : Scheme} {E : GeneralizedEllipticCurve S}
    (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)
    (b : Bool) (q : S ⟶ normalizedLocus n b)
    (h : (normalizedModuliMap n b).app (Opposite.op S) (ULift.up q) =
      Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) : Smooth E.curve.hom := by
  rw [normalizedModuliMap_eq_pullback] at h
  exact smooth_of_normalized_comparison n H b q (Quotient.exact h)

/-- A nonsmooth original family is outside the pointwise normalized moduli image. -/
theorem normalized_moduli_ne_of_not_smooth {S : Scheme} {E : GeneralizedEllipticCurve S}
    (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)
    (hs : ¬ Smooth E.curve.hom) (b : Bool) (q : S ⟶ normalizedLocus n b) :
    (normalizedModuliMap n b).app (Opposite.op S) (ULift.up q) ≠
      Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩ :=
  fun h ↦ hs (smooth_of_normalized_moduli_eq n H hc ha b q h)

end FLT.Mazur.CyclicCharacteristicAtlas
