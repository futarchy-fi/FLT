/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicNormalizedModuli

/-!
# Actual finite subgroups on the normalized characteristic charts

The normalized modular map is represented by the pulled-back universal full
curve and finite subgroup. Its fppf coverage therefore yields compatible
isomorphisms of actual subgroup schemes on every covering chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The full original DR curve restricted to the actual closed normalized chart. -/
def normalizedCurve (d : Bool) : GeneralizedEllipticCurve (normalizedLocus n d) :=
  (curve n d).baseChange (normalizedInclusion n d)

/-- The actual universal finite subgroup on the normalized characteristic chart. -/
def normalizedSubgroup (d : Bool) : (normalizedCurve n d).FiniteSubgroup n :=
  (subgroup n d).baseChange (normalizedInclusion n d)

/-- The actual normalized subgroup remains cyclic. -/
theorem normalizedSubgroup_isCyclic (d : Bool) : (normalizedSubgroup n d).IsCyclic :=
  (subgroup_isCyclic n d).baseChange (subgroup n d) (normalizedInclusion n d)

/-- The actual normalized subgroup remains ample. -/
theorem normalizedSubgroup_isAmple (d : Bool) : (normalizedSubgroup n d).IsAmple :=
  (subgroup_isAmple n d).baseChange (normalizedInclusion n d)

/-- The class of the actual normalized full curve and finite subgroup. -/
def normalizedModuliClass (d : Bool) : ampleCyclicClasses (normalizedLocus n d) n :=
  Quotient.mk _ ⟨⟨normalizedCurve n d, normalizedSubgroup n d⟩,
    normalizedSubgroup_isCyclic n d, normalizedSubgroup_isAmple n d⟩

/-- Each normalized test represents the actual pulled-back normalized subgroup. -/
theorem normalizedModuliMap_eq_pullback (d : Bool) {T : Scheme}
    (v : T ⟶ normalizedLocus n d) :
    (normalizedModuliMap n d).app (Opposite.op T) (ULift.up v) =
      ampleCyclicClassesPullback v n (normalizedModuliClass n d) := by
  have hv := normalizedModuliMap_normalization n d (v ≫ normalizedInclusion n d)
  rw [Category.assoc, normalizedInclusion_normalization, Category.comp_id] at hv
  rw [hv, ampleCyclicClassesPullback_comp]
  rfl

/-- The normalized charts cover full original smooth objects by actual compatible isomorphisms. -/
theorem exists_normalized_subgroup_fppf_cover {S : Scheme} {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (d : C.I₀ → Bool)
      (v : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (d i)),
      ∀ i, Nonempty (CompatibleIso ((normalizedSubgroup n (d i)).baseChange (v i))
        (H.baseChange (C.f i))) := by
  obtain ⟨C, d, v, hv⟩ := exists_normalized_moduli_fppf_cover n H hc ha
  refine ⟨C, d, v, fun i ↦ ?_⟩
  have hi := hv i
  rw [normalizedModuliMap_eq_pullback] at hi
  exact Quotient.exact hi

/-- A normalized relabeling preserves the actual full curve and subgroup up to compatibility. -/
theorem normalizedRelabel_subgroup {T : Scheme} (d : Bool)
    (v : T ⟶ normalizedLocus n d) (e : RelabelGroup n) :
    Nonempty (CompatibleIso
      ((normalizedSubgroup n d).baseChange (v ≫ (normalizedRelabelAction n d e).hom))
      ((normalizedSubgroup n d).baseChange v)) := by
  have he := normalizedModuliMap_action n d v e
  rw [normalizedModuliMap_eq_pullback, normalizedModuliMap_eq_pullback] at he
  exact Quotient.exact he

end FLT.Mazur.CyclicCharacteristicAtlas
