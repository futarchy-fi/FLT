/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullClass

/-!
# Compatible original points land in the full-intersection open

Pull back the actual Hilbert chart cover along a glued point. Each resulting
local point lies in its original full intersection, so their images lie in
the constructed union. No translation-base coordinate is prescribed or discarded.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
  (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))
  {W : Over (Spec (.of R))} (b : W ⟶ U) (k : W ⟶ baseMarkedGluedTest f hL V a)
  (hk : baseMarkedGluedPoint f hL V a W k = (relativeFppfSheaf f).obj.map b.op s)

include hk in
/-- Equality of the original Picard classes forces the pair into the full open union. -/
theorem baseMarkedFull_lift_range :
    Set.range (prod.lift b (k ≫ baseMarkedGluedBase f hL V a)).left ⊆
      Set.range (baseMarkedFullInclusion f V a U s).left := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, z, hz⟩ := Scheme.Cover.exists_eq
    ((baseMarkedGluedCover f hL V a).pullback₁ k.left) x
  let c := baseMarkedGluedArrow f hL V a i
  let E : Over (Spec (.of R)) := Over.mk (pullback.fst k.left c.left ≫ W.hom)
  let p : E ⟶ W := Over.homMk (pullback.fst k.left c.left) rfl
  let q : E ⟶ variableHilbertTest f (a i).1 V :=
    Over.homMk (pullback.snd k.left c.left) (by
      rw [← c.w, ← Category.assoc, ← pullback.condition, Category.assoc, k.w]
      rfl)
  have he : p ≫ k = q ≫ c := Over.OverMorphism.ext pullback.condition
  have hc : variableHilbertPoint f (a i).1 hL V (a i).2 E q =
      (relativeFppfSheaf f).obj.map (p ≫ b).op s := by
    rw [← baseMarkedGluedPoint_chart, ← he, baseMarkedGluedPoint_natural, hk]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  obtain ⟨l, hl, _⟩ := variableHilbertOverlap_lift f (a i).1 hL V (a i).2 U s (p ≫ b) q hc
  have hp : l ≫ variableHilbertOverlapArrow f (a i).1 V (a i).2 U s =
      p ≫ prod.lift b (k ≫ baseMarkedGluedBase f hL V a) := by
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst, variableHilbertOverlapToTest] using hl.1
    · simp only [Category.assoc, prod.lift_snd]
      rw [← variableHilbertOverlapToChart_base f hL (a i).1 V U (a i).2 s, ← Category.assoc, hl.2,
        ← baseMarkedGluedArrow_base f hL V a i, ← Category.assoc, ← he, Category.assoc]
  have hp' : (l ≫ baseMarkedFullChart f V a U s i) ≫
      baseMarkedFullInclusion f V a U s =
        p ≫ prod.lift b (k ≫ baseMarkedGluedBase f hL V a) := by
    rw [Category.assoc, baseMarkedFullChart_inclusion]
    exact hp
  refine ⟨(l ≫ baseMarkedFullChart f V a U s i).left z, ?_⟩
  change ((l ≫ baseMarkedFullChart f V a U s i) ≫
    baseMarkedFullInclusion f V a U s).left z = _
  rw [hp']
  change (prod.lift b (k ≫ baseMarkedGluedBase f hL V a)).left (p.left z) = _
  exact congrArg (prod.lift b (k ≫ baseMarkedGluedBase f hL V a)).left hz

end FLT.Mazur.HilbertChart
