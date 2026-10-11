/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientIndependentLineDescent
public import FLT.Mazur.RelativeAcyclicClassDivisor

/-!
# Full divisors for independently varying lines on coefficient tests

A proper flat geometrically integral finite-coefficient family supplies a
full divisor for every geometrically acyclic rank-one line on its arbitrary
ring test. The line is descended by construction, not supplied as model data.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve Approximation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CommRing A] (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
  {X Y : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ Spec (.of A)}
  {q : Y ⟶ Spec (.of R)} [IsProper q] [Flat q] [GeometricallyIntegral q]
  (h : IsPullback a f q (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
  (L : X.Modules) (hL : LocallyFreeRankOne L)

omit [GeometricallyIntegral q] in
include h hL in
/-- The actual direct image criterion holds for any independently chosen test line. -/
theorem coefficientLine_geometricAcyclicRankOne_iff_actual :
    GeometricAcyclicRankOne f L ↔ AcyclicRankOne f L := by
  obtain ⟨i, M, hM, ⟨e⟩⟩ := exists_coefficient_independent_line_cartesian R q h L hL
  let _ : Algebra.FiniteType ℤ i.unop.val := i.unop.property.2
  let _ : IsNoetherianRing i.unop.val := Algebra.FiniteType.isNoetherianRing ℤ i.unop.val
  let _ : IsLocallyNoetherian ((coefficientSpectrumDiagram R).obj i) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of i.unop.val)))
  exact (geometricAcyclicRankOne_iso f e).symm.trans
    ((geometricAcyclicRankOne_iff_actual _ (coefficientModelRecovery_isPullback h i) M hM).trans
      (acyclicRankOne_iso f e))

include h in
/-- Approximation constructs a full relative Cartier divisor for every acyclic test line. -/
theorem coefficientLine_relativeFiber_nonempty (hA : GeometricAcyclicRankOne f L) :
    Nonempty (RelativeFiber f L hL) := by
  obtain ⟨i, M, hM, ⟨e⟩⟩ := exists_coefficient_independent_line_cartesian R q h L hL
  let _ : Algebra.FiniteType ℤ i.unop.val := i.unop.property.2
  let _ : IsNoetherianRing i.unop.val := Algebra.FiniteType.isNoetherianRing ℤ i.unop.val
  let _ : IsLocallyNoetherian ((coefficientSpectrumDiagram R).obj i) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of i.unop.val)))
  have hA' := (geometricAcyclicRankOne_iso f e).mpr hA
  have hN := (geometricAcyclicRankOne_iff_actual _
    (coefficientModelRecovery_isPullback h i) M hM).mp hA'
  exact ⟨relativeFiberCoefficientEquiv f (hM.pullback _) hL e
    (acyclicRankOneFamilyDivisor (coefficientModelRecovery_isPullback h i) M hM hN.1 hN.2)⟩

/-- The actual full divisor, with the independently specified test line as its Abel class. -/
def coefficientLineDivisor (hA : GeometricAcyclicRankOne f L) : RelativeFiber f L hL :=
  (coefficientLine_relativeFiber_nonempty R h L hL hA).some

/-- All relative Cartier competitors have the same full ideal. -/
theorem coefficientLineDivisor_unique (hA : GeometricAcyclicRankOne f L)
    (D : RelativeFiber f L hL) : D = coefficientLineDivisor R h L hL hA := by
  let _ : Surjective f := MorphismProperty.of_isPullback h inferInstance
  let _ := rankOne_relativeFiber_subsingleton f L hL
    ((coefficientLine_geometricAcyclicRankOne_iff_actual R h L hL).mp hA).2
  exact Subsingleton.elim _ _

end FLT.Mazur.CartierAbel
