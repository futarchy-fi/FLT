/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedProjectiveHilbertParameter

/-!
# Naturality and symmetry of the ordered Hilbert morphism

Specializing the ordered universal tuple gives exactly the Hilbert parameter
of the supplied tuple. Consequently every coordinate permutation fixes the
actual morphism from the ordered parameter space to the Hilbert scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.HilbertChart

namespace FLT.Mazur.OrderedCurvePower

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {Z : Scheme} (z : Z ⟶ Spec (.of R))
variable [SmoothOfRelativeDimension 1 z] [IsProper z]
variable {B : Type} [CommRing B] {ι : Type}
variable (e : Z ⟶ ProjectiveSpace.space B ι) [IsClosedImmersion e] (d : ℕ)
variable {X Y : Scheme} (s : X ⟶ Spec (.of R))
variable (x : Fin d → (X ⟶ Z)) (hx : ∀ i, x i ≫ z = s)

/-- Arbitrary base change of an ordered tuple gives the composite classifying morphism. -/
theorem tupleHilbertParameter_natural (t : Y ⟶ Spec (.of R)) (g : Y ⟶ X)
    (hg : g ≫ s = t) :
    tupleHilbertParameter z e d t (fun i ↦ g ≫ x i)
        (fun i ↦ by rw [Category.assoc, hx i, hg]) =
      ⟨g ≫ (tupleHilbertParameter z e d s x hx).val, by
        rw [Category.assoc, (tupleHilbertParameter z e d s x hx).property, hg]⟩ := by
  apply (allAffineAmbientCharts z).parameterFamily_injective d t
  rw [tupleHilbertParameter_family, ← AmbientQuotientCharts.parameterFamily_natural,
    tupleHilbertParameter_family, tupleRelativeIdealFamily_baseChange]
  exact hg

/-- The universal ordered Hilbert morphism specializes to the parameter of every tuple. -/
theorem orderedHilbertParameter_specialize :
    classify z d s x hx ≫ (orderedHilbertParameter z e d).val =
      (tupleHilbertParameter z e d s x hx).val := by
  have h := tupleHilbertParameter_natural z e d (base z d) (point z d) (point_base z d)
    s (classify z d s x hx) (classify_base z d s x hx)
  simp only [classify_point] at h
  exact congrArg Subtype.val h.symm

/-- Every coordinate permutation fixes the actual ordered-to-Hilbert morphism. -/
theorem orderedHilbertParameter_reindex (σ : Equiv.Perm (Fin d)) :
    reindex z d σ ≫ (orderedHilbertParameter z e d).val =
      (orderedHilbertParameter z e d).val := by
  have h := orderedHilbertParameter_specialize z e d (base z d)
    (fun i ↦ point z d (σ i)) (fun i ↦ point_base z d (σ i))
  rw [tupleHilbertParameter_permutation] at h
  exact h

end FLT.Mazur.OrderedCurvePower
