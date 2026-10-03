/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkedSections
public import FLT.Mazur.SectionSumFinite

/-!
# Boundary divisors meeting every polygon component

One unit on each Laurent component defines a finite flat relative Cartier
divisor on the specified polygon. Its actual support meets every irreducible
component. The all-one choice is a candidate for a constant cyclic level;
subgroup operations, rank and cyclicity are separate obligations.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonBoundaryDivisor
open PolygonPinching PolygonMarkedSections FCurve
variable (K : Type u) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)

/-- The sum of the section divisors, retaining their actual ideal sheaves. -/
def ideal (a : Fin n → Kˣ) : C.left.IdealSheafData :=
  ∏ i, (sectionMap K n p (a i) i).ker

variable (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- The section sum is a relative effective Cartier divisor. -/
theorem cartier (a : Fin n → Kˣ) : RelativeEffectiveCartier C.hom (ideal K n p a) :=
  relativeEffectiveCartier_prod C.hom Finset.univ _ fun i _ ↦
    section_cartier K n p hn q h (a i) i

include h in
/-- The boundary divisor is finite over the base field. -/
theorem finite (a : Fin n → Kˣ) : IsFinite ((ideal K n p a).subschemeι ≫ C.hom) := by
  let := PolygonProper.proper K n hn p q h
  exact isFinite_section_prod C.hom Finset.univ (fun i ↦ sectionMap K n p (a i) i)
    (fun i _ ↦ section_base K n p (a i) i)

include h in
/-- The boundary divisor is flat over the base field. -/
theorem flat (a : Fin n → Kˣ) : Flat ((ideal K n p a).subschemeι ≫ C.hom) :=
  (cartier K n p hn q h a).2

include h in
/-- The divisor support consists exactly of the marked section images. -/
theorem mem_support_iff (a : Fin n → Kˣ) (x : C.left) :
    x ∈ (ideal K n p a).support ↔ ∃ i, x ∈ Set.range (sectionMap K n p (a i) i) := by
  let := PolygonSeparated.cocone K n hn p q h
  change x ∈ (∏ i ∈ Finset.univ, (sectionMap K n p (a i) i).ker).support ↔ _
  rw [mem_support_prod]
  simp only [Finset.mem_univ, true_and]
  simp only [← SetLike.mem_coe, support_section_ker C.hom _ (section_base K n p _ _)]

include h in
/-- Every actual irreducible component meets the boundary divisor support. -/
theorem meetsEveryComponent (a : Fin n → Kˣ) : MeetsEveryComponent (ideal K n p a) := by
  intro Z hZ
  rw [PolygonComponentImages.components_eq K n hn p q h] at hZ
  obtain ⟨i, rfl⟩ := hZ
  let x : Spec (.of K) := Classical.choice inferInstance
  refine ⟨sectionMap K n p (a i) i x, ?_, ?_⟩
  · exact ⟨(torusToComponent K).left (ProjectiveLineActionSpecialization.unitPoint K (a i) x),
      rfl⟩
  · exact (mem_support_iff K n p hn q h a _).mpr ⟨i, x, rfl⟩

end FLT.Mazur.PolygonBoundaryDivisor
