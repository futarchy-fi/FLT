/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterFiniteCoefficientModel
public import FLT.Mazur.CommonCoefficientStage

/-!
# Independent character coefficient models agree in a common finite subring

The comparison uses literal inclusions into the original ring. It retains
all character coefficients over arbitrary rings, including nilpotents.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.CharacterCoefficientCommonRefinement
variable {R G : Type*} [CommRing R] [AddCommMonoid G]

/-- Change character coefficients along an actual subalgebra inclusion. -/
def inclusion {A B : Subalgebra ℤ R} (h : A ≤ B) :
    AddMonoidAlgebra A G →+* AddMonoidAlgebra B G :=
  AddMonoidAlgebra.mapRingHom G (Subalgebra.inclusion h).toRingHom

/-- Coefficient inclusion is injective even when the original ring is nonreduced. -/
theorem inclusion_injective {A B : Subalgebra ℤ R} (h : A ≤ B) :
    Function.Injective (inclusion (G := G) h) :=
  AddMonoidAlgebra.map_injective _ (Subalgebra.inclusion_injective h)

/-- Two independent representatives of the same original element agree in any common subring. -/
theorem inclusion_eq_of_recovery {A B C : Subalgebra ℤ R} (hA : A ≤ C) (hB : B ≤ C)
    (a : AddMonoidAlgebra A G) (b : AddMonoidAlgebra B G)
    (h : AddMonoidAlgebra.mapRingHom G A.val.toRingHom a =
      AddMonoidAlgebra.mapRingHom G B.val.toRingHom b) :
    inclusion hA a = inclusion hB b := by
  apply AddMonoidAlgebra.map_injective C.val.toAddMonoidHom Subtype.val_injective
  change (AddMonoidAlgebra.mapRingHom G C.val.toRingHom).comp (inclusion hA) a =
    (AddMonoidAlgebra.mapRingHom G C.val.toRingHom).comp (inclusion hB) b
  have hA' : C.val.toRingHom.comp (Subalgebra.inclusion hA).toRingHom = A.val.toRingHom := by
    ext x
    rfl
  have hB' : C.val.toRingHom.comp (Subalgebra.inclusion hB).toRingHom = B.val.toRingHom := by
    ext x
    rfl
  simpa only [inclusion, ← AddMonoidAlgebra.mapRingHom_comp, hA', hB'] using h

/-- Entire coordinate homomorphisms agree after refinement when their original recoveries agree. -/
theorem inclusion_comp_eq_of_recovery {A B C : Subalgebra ℤ R}
    (hA : A ≤ C) (hB : B ≤ C) {T : Type*} [Semiring T]
    (a : T →+* AddMonoidAlgebra A G) (b : T →+* AddMonoidAlgebra B G)
    (h : (AddMonoidAlgebra.mapRingHom G A.val.toRingHom).comp a =
      (AddMonoidAlgebra.mapRingHom G B.val.toRingHom).comp b) :
    (inclusion hA).comp a = (inclusion hB).comp b := by
  apply RingHom.ext
  intro x
  exact inclusion_eq_of_recovery hA hB (a x) (b x) (RingHom.congr_fun h x)

/-- Independent finite coefficient models have a common finite comparison retaining all elements. -/
theorem exists_common_character_coefficients (A B : Subalgebra ℤ R)
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType ℤ B] :
    ∃ (C : Subalgebra ℤ R) (_ : Algebra.FiniteType ℤ C) (hA : A ≤ C) (hB : B ≤ C),
      ∀ (a : AddMonoidAlgebra A G) (b : AddMonoidAlgebra B G),
        AddMonoidAlgebra.mapRingHom G A.val.toRingHom a =
          AddMonoidAlgebra.mapRingHom G B.val.toRingHom b →
            inclusion hA a = inclusion hB b := by
  obtain ⟨C, hC, _, hA, hB⟩ := Approximation.exists_common_coefficient_extension A
    (fun _ : Unit => B) (fun _ => inferInstance) ∅ Set.finite_empty
  exact ⟨C, hC, hA, hB (), fun a b h => inclusion_eq_of_recovery hA (hB ()) a b h⟩

end FLT.Mazur.CharacterCoefficientCommonRefinement
