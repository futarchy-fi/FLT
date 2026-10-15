/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurvePowerSmooth
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Geometric irreducibility of the original ordered translation parameters

The empty power and every successor are geometrically irreducible over the
unchanged base. The result applies to arbitrary field extensions and to
specified cartesian fibers, not just the chosen categorical pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OrderedCurvePower
variable {X S : Scheme} (f : X ⟶ S) [Smooth f] [GeometricallyIrreducible f]

omit [Smooth f] in
/-- Forgetting the first ordered point has geometrically irreducible fibers. -/
theorem tail_geometricallyIrreducible (n : ℕ) : GeometricallyIrreducible (tail f n) :=
  MorphismProperty.of_isPullback (successor_isPullback f n) inferInstance

/-- The original ordered parameter scheme is geometrically irreducible over its base. -/
theorem base_geometricallyIrreducible (n : ℕ) : GeometricallyIrreducible (base f n) := by
  induction n with
  | zero =>
    let _ : IsIso (base f 0) := inferInstanceAs (IsIso (emptyIso f).hom)
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ g ↦ ?_⟩
    exact (asIso (pullback.snd (base f 0) g)).hom.homeomorph.irreducibleSpace_iff.mpr
      inferInstance
  | succ n hn =>
    let _ := hn
    let _ := base_smooth f n
    let _ := tail_smooth f n
    let _ := tail_geometricallyIrreducible f n
    rw [← tail_base f n]
    exact GeometricallyIrreducible.comp _ _

/-- Every specified field fiber of the ordered parameter scheme is irreducible. -/
theorem originalFiber_irreducible (n : ℕ) {K : Type} [Field K] (g : Spec (.of K) ⟶ S)
    {Y : Scheme} {a : Y ⟶ space f n} {b : Y ⟶ Spec (.of K)}
    (H : IsPullback a b (base f n) g) : IrreducibleSpace Y := by
  let _ := base_geometricallyIrreducible f n
  exact GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ H

end FLT.Mazur.OrderedCurvePower
