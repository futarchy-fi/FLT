/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicAdicParameterQuotient
public import FLT.Mazur.OneGonAdicPuncturedModuli

/-!
# Actual smooth coverage, prescribed boundary classes, and generic overlaps

All smooth original ample cyclic families are covered by the enlarged quotient.
Every prescribed original field one-gon subgroup is its actual adic boundary.
On the genuine generic fiber, the smooth and adic representatives are related by
full compatible isomorphisms. No coverage of arbitrary singular bases is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicAdicParameters
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CyclicCharacteristicAtlas IntegralOneGonSpecializations
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The enlarged quotient class of an actual test of the integral degeneration. -/
def adicClass {T : Scheme} (q : T ⟶ OneGonAdicModuliChart.base) : ParameterClasses n T :=
  Quotient.mk _ ⟨none, ULift.up q⟩

/-- Every adic restriction retains its original parameter in the full quotient. -/
theorem adicClass_pullback {T U : Scheme} (q : T ⟶ OneGonAdicModuliChart.base)
    (g : U ⟶ T) : (classPresheaf n).map g.op (adicClass n q) = adicClass n (g ≫ q) := rfl

/-- The adic quotient class maps to the actual complete-base modular class. -/
theorem adicClass_moduli {T : Scheme} (q : T ⟶ OneGonAdicModuliChart.base) :
    classMap n T (adicClass n q) =
      (OneGonAdicModuliChart.moduliMap n).app (Opposite.op T) (ULift.up q) := rfl

/-- Every original smooth ample cyclic family is in the enlarged quotient image fppf locally. -/
theorem smooth_cover {S : Scheme} {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (z : ∀ i, ParameterClasses n (C.X i)),
      ∀ i, classMap n (C.X i) (z i) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, b, q, hq⟩ := exists_normalized_moduli_fppf_cover n H hc ha
  refine ⟨C, fun i ↦ Quotient.mk _ ⟨some (b i), ULift.up (q i)⟩, fun i ↦ ?_⟩
  exact (normalizedModuliMap_eq_pullback n (b i) (q i)).symm.trans (hq i)

/-- The actual generic smoothing has genuine mixed smooth-adic compatible comparisons. -/
theorem generic_related_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of GenericField)))
      (b : C.I₀ → Bool) (q : ∀ i, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, Related n ⟨some (b i), ULift.up (q i)⟩
        ⟨none, ULift.up (C.f i ≫ genericMap)⟩ := by
  obtain ⟨C, b, q, hq⟩ := OneGonAdicModuliChart.generic_normalized_cover n
  refine ⟨C, b, q, fun i ↦ (related_iff_class_eq n _ _).mpr ?_⟩
  exact (normalizedModuliMap_eq_pullback n (b i) (q i)).symm.trans (hq i)

/-- On the genuine generic fiber both families have the same enlarged quotient sections. -/
theorem generic_quotient_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of GenericField)))
      (b : C.I₀ → Bool) (q : ∀ i, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, (Quotient.mk _ ⟨some (b i), ULift.up (q i)⟩ : ParameterClasses n (C.X i)) =
        (classPresheaf n).map (C.f i).op (adicClass n genericMap) := by
  obtain ⟨C, b, q, hq⟩ := generic_related_cover n
  exact ⟨C, b, q, fun i ↦ Quotient.sound (hq i)⟩

/-- The entire actual punctured family has full mixed compatible comparisons. -/
theorem punctured_related_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage
        (Spec (.of (OneGonSmoothing.PuncturedRing ℤ))))
      (b : C.I₀ → Bool) (q : ∀ i, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, Related n ⟨some (b i), ULift.up (q i)⟩
        ⟨none, ULift.up (C.f i ≫ OneGonSmoothing.puncturedBaseInclusion ℤ)⟩ := by
  obtain ⟨C, b, q, hq⟩ := OneGonAdicModuliChart.punctured_normalized_cover n
  refine ⟨C, b, q, fun i ↦ (related_iff_class_eq n _ _).mpr ?_⟩
  exact (normalizedModuliMap_eq_pullback n (b i) (q i)).symm.trans (hq i)

/-- On all of D(X), the actual adic quotient section has smooth local representatives. -/
theorem punctured_quotient_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage
        (Spec (.of (OneGonSmoothing.PuncturedRing ℤ))))
      (b : C.I₀ → Bool) (q : ∀ i, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, (Quotient.mk _ ⟨some (b i), ULift.up (q i)⟩ : ParameterClasses n (C.X i)) =
        (classPresheaf n).map (C.f i).op
          (adicClass n (OneGonSmoothing.puncturedBaseInclusion ℤ)) := by
  obtain ⟨C, b, q, hq⟩ := punctured_related_cover n
  exact ⟨C, b, q, fun i ↦ Quotient.sound (hq i)⟩

variable (K : Type) [Field K]
  (H : (PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).FiniteSubgroup n)

/-- Every prescribed original one-gon subgroup is represented by the actual adic boundary. -/
theorem prescribed_boundary_class (hc : H.IsCyclic) (ha : H.IsAmple) :
    classMap n (Spec (.of K)) (adicClass n (boundaryMap K)) =
      Quotient.mk _ (⟨⟨_, H⟩, hc, ha⟩ : ampleCyclicLevels (Spec (.of K)) n) :=
  OneGonAdicCharacterTower.integralCanonicalLevelClass_boundary n K H hc ha

end FLT.Mazur.CyclicAdicParameters
