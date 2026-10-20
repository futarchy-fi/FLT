/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryModuliMap
public import FLT.Mazur.SchemeSmoothFppfFamilyDescent

/-!
# Exact fppf coverage scope of the normalized characteristic atlas

An original ample cyclic family has a normalized fppf presentation exactly
when its whole curve is smooth. The actual split polygon boundary classes
therefore cannot be covered by these charts, even after fppf refinement.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {S : Scheme} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)

/-- An actual normalized fppf presentation forces smoothness of the original whole curve. -/
theorem smooth_of_normalized_fppf_cover
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
    (q : ∀ i, C.X i ⟶ normalizedLocus n (b i))
    (hq : ∀ i, (normalizedModuliMap n (b i)).app (Opposite.op (C.X i)) (ULift.up (q i)) =
      ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) :
    Smooth E.curve.hom := by
  apply SchemeFppfFamily.smooth_of_cover E.curve.hom C
  intro i
  exact smooth_of_normalized_moduli_eq n (H.baseChange (C.f i))
    (hc.baseChange H (C.f i)) (ha.baseChange (C.f i)) (b i) (q i) (hq i)

/-- Both directions of the precise normalized fppf coverage criterion. -/
theorem normalized_fppf_cover_iff_smooth :
    (∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (q : ∀ i, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, (normalizedModuliMap n (b i)).app (Opposite.op (C.X i)) (ULift.up (q i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩)) ↔
      Smooth E.curve.hom := by
  constructor
  · rintro ⟨C, b, q, hq⟩
    exact smooth_of_normalized_fppf_cover n H hc ha C b q hq
  · intro hs
    let _ := hs
    exact exists_normalized_moduli_fppf_cover n H hc ha

/-- The actual split boundary level has no normalized fppf covering presentation. -/
theorem boundary_no_normalized_fppf_cover (K : Type) [Field K]
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of K))) (b : C.I₀ → Bool)
    (q : ∀ i, C.X i ⟶ normalizedLocus n (b i)) :
    ¬ (∀ i, (normalizedModuliMap n (b i)).app (Opposite.op (C.X i)) (ULift.up (q i)) =
      ampleCyclicClassesPullback (C.f i) n (PolygonBoundaryModuli.boundaryClass K n)) := by
  intro hq
  exact PolygonBoundaryModuli.boundaryCurve_not_smooth K n
    (smooth_of_normalized_fppf_cover n (PolygonBoundaryModuli.boundaryLevel K n).val.2
      (PolygonBoundaryModuli.boundaryLevel K n).property.1
      (PolygonBoundaryModuli.boundaryLevel K n).property.2 C b q hq)

end FLT.Mazur.CyclicCharacteristicAtlas
