/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedSubsets
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# A proper curve endomorphism is surjective or constant

A proper irreducible image in a curve is a singleton. Over an algebraically
closed field, equality on closed points upgrades this topological statement
to equality of morphisms from the reduced curve.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (s : X ⟶ Spec (.of K)) [IsProper s]
  (hd : topologicalKrullDim X ≤ 1) (e : Spec (.of K) ⟶ X) (he : e ≫ s = 𝟙 _)
  (f : X ⟶ X) (hf : f ≫ s = s)

include hd he hf in
/-- An endomorphism of a proper integral curve is onto or constant at its chosen point image. -/
theorem curveEndomorphism_surjective_or_constant :
    Function.Surjective f ∨ f = s ≫ e ≫ f := by
  let _ : IsProper (f ≫ s) := hf.symm ▸ inferInstance
  let _ : IsProper f := IsProper.of_comp f s
  by_cases hs : Function.Surjective f
  · exact Or.inl hs
  right
  obtain ⟨z, hz⟩ := eq_singleton_of_isClosed_of_isIrreducible hd
    f.isClosedMap.isClosed_range (by
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn)
    (fun hh ↦ hs (Set.range_eq_univ.mp hh))
  have hall (x : X) : f x = z := by
    have hx : f x ∈ Set.range f := ⟨x, rfl⟩
    rwa [hz, Set.mem_singleton_iff] at hx
  apply ext_of_apply_eq s Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ _
    exact (hall x).trans (hall (e (s x))).symm
  · rw [Category.assoc, Category.assoc, hf, he, Category.comp_id]

include hf in
omit [IsIntegral X] in
/-- A surjective endomorphism over an algebraically closed field lifts every rational point. -/
theorem curveEndomorphism_rationalPoint_lift (hs : Function.Surjective f)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ s = 𝟙 _) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ s = 𝟙 _ ∧ q ≫ f = p := by
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  let z := p (IsLocalRing.closedPoint K)
  have hz : IsClosed ({z} : Set X) := (pointEquivClosedPoint s ⟨p, hp⟩).property
  obtain ⟨x, hx⟩ := hs z
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    (show (f ⁻¹' {z}).Nonempty from ⟨x, hx⟩)
    (hz.preimage f.continuous).isLocallyClosed
  change IsClosed {y} at hyc
  refine ⟨pointOfClosedPoint s y hyc, pointOfClosedPoint_comp s y hyc, ?_⟩
  apply ext_of_apply_closedPoint_eq s
  · rw [Category.assoc, hf, pointOfClosedPoint_comp]
  · exact hp
  · change f (pointOfClosedPoint s y hyc _) = _
    rw [pointOfClosedPoint_apply]
    exact hy

end FLT.Mazur.FCurve
