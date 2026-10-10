/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineCoordinateCover
public import FLT.Mazur.SectionLinePointOverlapEquality

/-!
# Coordinate normalization under base change and changes of line frame

The local normalized submodule of a split generator commutes with every
coefficient map. Multiplication of the original line frame by a unit leaves
the actual image submodule, and hence its actual projective point, unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
variable {R S : Type u} [CommRing R] [CommRing S] {ι : Type u}

/-- Normalizing an actual image line commutes with every coefficient extension. -/
lemma baseChange_unitCoordinateLine (φ : R →+* S) (v : ι → R) (i : ι)
    (a : Rˣ) (hi : v i = a) :
    baseChange φ i (unitCoordinateLine v i a hi) =
      unitCoordinateLine (fun j ↦ φ (v j)) i (Units.map φ.toMonoidHom a)
        (congrArg φ hi) := by
  apply (tupleEquiv S ι i).symm.injective
  apply Subtype.ext
  change generator S ι i _ = generator S ι i _
  rw [generator_baseChange, unitCoordinateLine_generator, unitCoordinateLine_generator]
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← map_inv, Units.coe_map]
  rfl

/-- Unit rescaling of the original generator preserves its actual image submodule. -/
lemma generatorRange_unit_smul (v : ι → R) (a : Rˣ) :
    LinearMap.range (LinearMap.toSpanSingleton R (ι → R) ((a : R) • v)) =
      LinearMap.range (LinearMap.toSpanSingleton R (ι → R) v) := by
  apply le_antisymm
  · rintro w ⟨b, rfl⟩
    exact ⟨b * a, by simp only [LinearMap.toSpanSingleton_apply, smul_smul]⟩
  · rintro w ⟨b, rfl⟩
    refine ⟨b * ↑a⁻¹, ?_⟩
    simp only [LinearMap.toSpanSingleton_apply, smul_smul, mul_assoc, Units.inv_mul, mul_one]

/-- Two unit coordinates normalize the same actual image line. -/
lemma unitCoordinateLine_val_eq (v : ι → R) (i j : ι) (a b : Rˣ)
    (hi : v i = a) (hj : v j = b) :
    (unitCoordinateLine v i a hi).val = (unitCoordinateLine v j b hj).val := rfl

/-- Changing a trivialization of the original line preserves its normalized image. -/
lemma unitCoordinateLine_smul_val (v : ι → R) (i j : ι) (a b c : Rˣ)
    (hi : v i = a) (hj : v j = b) :
    (unitCoordinateLine ((c : R) • v) i (c * a)
      (by simp only [Pi.smul_apply, smul_eq_mul, hi, Units.val_mul])).val =
        (unitCoordinateLine v j b hj).val := generatorRange_unit_smul v c

/-- Actual projective points are independent of the chosen local line frame. -/
lemma unitCoordinateLine_smul_point {A : Type u} [CommRing A] (φ : A →+* R)
    (v : ι → R) (i j : ι) (a b c : Rˣ) (hi : v i = a) (hj : v j = b) :
    ProjectiveSpace.sectionLinePoint A ι φ i
      (unitCoordinateLine ((c : R) • v) i (c * a)
        (by simp only [Pi.smul_apply, smul_eq_mul, hi, Units.val_mul])) =
      ProjectiveSpace.sectionLinePoint A ι φ j (unitCoordinateLine v j b hj) :=
  projectivePoint_change R ι φ i j _ _ (unitCoordinateLine_smul_val v i j a b c hi hj)

end FLT.Mazur.NormalizedSectionLine
