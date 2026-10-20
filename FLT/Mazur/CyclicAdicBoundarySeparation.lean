/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicAdicCoverage
public import FLT.Mazur.CyclicCharacteristicFppfScope
public import FLT.Mazur.PolygonNodeLocus

/-!
# The actual adic boundary is outside the old smooth quotient

The added boundary class is a genuine new modular object: its one-gon node
prevents any compatible smooth normalized parameter, even though the generic
fiber has the mixed comparisons constructed in CyclicAdicCoverage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicAdicParameters
open GeneralizedEllipticCurve.FiniteSubgroup CyclicCharacteristicAtlas
open IntegralOneGonSpecializations
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (K : Type) [Field K]
  (H : (PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).FiniteSubgroup n)

/-- The original one-gon curve has a node at every field-valued boundary test. -/
theorem oneGon_not_smooth : ¬ Smooth (OneGonGluing.toBase K) := by
  intro hs
  let _ := hs
  have hn := PolygonNodeLocus.one_not_smooth K (default : Spec (.of K))
  dsimp only at hn
  have he : (OneGonGluing.toBase K).smoothLocus = ⊤ :=
    (OneGonGluing.toBase K).smoothLocus_eq_top
  rw [he] at hn
  exact hn trivial

/-- No old normalized smooth parameter represents the actual adic boundary. -/
theorem normalized_ne_adic_boundary (hc : H.IsCyclic) (ha : H.IsAmple)
    (b : Bool) (q : Spec (.of K) ⟶ normalizedLocus n b) :
    (normalizedModuliMap n b).app (Opposite.op (Spec (.of K))) (ULift.up q) ≠
      classMap n (Spec (.of K)) (adicClass n (boundaryMap K)) := by
  rw [prescribed_boundary_class n K H hc ha]
  exact normalized_moduli_ne_of_not_smooth n H hc ha (oneGon_not_smooth K) b q

/-- The boundary section is not in the image of the embedded original smooth quotient. -/
theorem adic_boundary_not_in_smooth_range (hc : H.IsCyclic) (ha : H.IsAmple) :
    adicClass n (boundaryMap K) ∉
      Set.range ((smoothClassInclusion n).app (Opposite.op (Spec (.of K)))) := by
  rintro ⟨z, hz⟩
  induction z using Quotient.inductionOn with | h q =>
    apply normalized_ne_adic_boundary n K H hc ha q.1 q.2.down
    have h := congrArg (classMap n (Spec (.of K))) hz
    exact (normalizedModuliMap_eq_pullback n q.1 q.2.down).trans h

/-- The actual boundary cannot acquire an old smooth presentation after fppf refinement. -/
theorem adic_boundary_no_smooth_fppf_cover (hc : H.IsCyclic) (ha : H.IsAmple)
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of K))) (b : C.I₀ → Bool)
    (q : ∀ i, C.X i ⟶ normalizedLocus n (b i)) :
    ¬ (∀ i, (normalizedModuliMap n (b i)).app (Opposite.op (C.X i)) (ULift.up (q i)) =
      ampleCyclicClassesPullback (C.f i) n
        (classMap n (Spec (.of K)) (adicClass n (boundaryMap K)))) := by
  intro hq
  rw [prescribed_boundary_class n K H hc ha] at hq
  exact oneGon_not_smooth K (smooth_of_normalized_fppf_cover n H hc ha C b q hq)

end FLT.Mazur.CyclicAdicParameters
