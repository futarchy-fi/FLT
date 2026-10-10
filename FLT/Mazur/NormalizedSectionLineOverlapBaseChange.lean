/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineSheafOverlap
public import FLT.Mazur.NormalizedSectionLineSheafBaseChange

/-!
# Scalar extension of section-line overlaps

Equal line submodules remain equal under arbitrary scalar extension, even
when different invertible coordinates are used. Their actual sheaf chart
comparisons commute with the constructed pullback comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
variable {R S : Type u} [CommRing R] [CommRing S] {ι : Type u}

/-- Extension preserves containment, independently of the chosen normalized coordinate. -/
lemma baseChange_val_le (φ : R →+* S) (i j : ι) (L : Chart R ι i) (M : Chart R ι j)
    (h : L.val ≤ M.val) : (baseChange φ i L).val ≤ (baseChange φ j M).val := by
  rintro v ⟨a, rfl⟩
  exact (baseChange φ j M).val.smul_mem a
    (coefficient_mem φ j M ⟨generator R ι i L, h (generator_mem R ι i L)⟩)

/-- Scalar extension preserves the actual line on a coordinate overlap. -/
lemma baseChange_val_eq (φ : R →+* S) (i j : ι) (L : Chart R ι i) (M : Chart R ι j)
    (h : L.val = M.val) : (baseChange φ i L).val = (baseChange φ j M).val :=
  le_antisymm (baseChange_val_le φ i j L M h.le)
    (baseChange_val_le φ j i M L h.ge)

/-- The normalized overlap unit extends by the original ring map. -/
lemma transitionUnit_baseChange (φ : R →+* S) (i j : ι) (L : Chart R ι i)
    (M : Chart R ι j) (h : L.val = M.val) :
    transitionUnit S ι i j (baseChange φ i L) (baseChange φ j M)
        (baseChange_val_eq φ i j L M h) =
      Units.map φ.toMonoidHom (transitionUnit R ι i j L M h) := by
  apply Units.ext
  exact congrFun (generator_baseChange φ i L) j

attribute [local irreducible] sheafBaseChange vectorSheafBaseChange sheafChartChange
attribute [local irreducible] Scheme.Modules.pullback

/-- Chart changes commute with actual sheaf base change through their ambient inclusions. -/
lemma sheafChartChange_baseChange [Finite ι] (φ : R →+* S) (i j : ι)
    (L : Chart R ι i) (M : Chart R ι j) (h : L.val = M.val) :
    (sheafBaseChange φ i L).hom ≫
        (sheafChartChange i j (baseChange φ i L) (baseChange φ j M)
          (baseChange_val_eq φ i j L M h)).hom =
      (pullback (Spec.map (CommRingCat.ofHom φ))).map (sheafChartChange i j L M h).hom ≫
        (sheafBaseChange φ j M).hom := by
  apply (cancel_mono (sheafInclusion j (baseChange φ j M))).mp
  simp only [Category.assoc, sheafChartChange_inclusion, sheafBaseChange_inclusion]
  rw [← Category.assoc, ← Functor.map_comp, sheafChartChange_inclusion]

end FLT.Mazur.NormalizedSectionLine
