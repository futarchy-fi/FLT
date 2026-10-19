/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedStrictExtension
public import FLT.Mazur.EquivalenceRelationCompleteScalarFiber
public import FLT.Mazur.SchemeFiniteGroupGeometricTests

/-!
# Fixed completeness tests and original geometric frame extensions

Complete frames annihilate the fixed tests by their actual closed-locus
geometry. A nonzero test constructs an extra normalized original arrow over
the same field, preserving all old coordinates and the original endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [TopologicalSpace.NoetherianSpace U.toScheme]
  {K : Type} [Field K] (w : Γ(U.toScheme, ⊤) →+* K)
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "u" => sourceCharacterMap w ≫ U.ι
local notation "tests" => completeAffineOrbitTests e I o U hU

/-- The actual complete-frame geometry forces each original character value to vanish. -/
theorem complete_character_tests_vanish (hu : Complete I o u) :
    ∀ t ∈ tests, w t.val = 0 := by
  apply source_character_tests_vanish ρ
    (U.ι ⁻¹' completePointLocus (p := p) (q := q) I o)
    (completeChart_isClosed I o U) (completeChart_stable e I o U hU) w
  exact (complete_iff_mem_completePointLocus I o u).mp hu

/-- Transport from a complete original frame proves test vanishing using the full relation. -/
theorem original_arrow_character_tests_vanish
    (v : Spec (.of K) ⟶ source p q I o) (hv : Complete I o v)
    (a : Spec (.of K) ⟶ D)
    (ha : a ≫ p = v ≫ first p q I o) (hb : a ≫ q = u ≫ first p q I o) :
    ∀ t ∈ tests, w t.val = 0 :=
  complete_character_tests_vanish e I o U hU w
    (complete_of_original_arrow e I o v u a ha hb hv)

/-- A nonzero test rules out every original arrow from any complete frame of the same size. -/
theorem nonzero_test_no_complete_arrow
    (t : invariantCoordinates ρ) (ht : t ∈ tests) (hnt : w t.val ≠ 0)
    (v : Spec (.of K) ⟶ source p q I o) (hv : Complete I o v) :
    ¬ ∃ a : Spec (.of K) ⟶ D,
      a ≫ p = v ≫ first p q I o ∧ a ≫ q = u ≫ first p q I o := by
  rintro ⟨a, ha, hb⟩
  exact hnt (original_arrow_character_tests_vanish e I o U hU w v hv a ha hb t ht)

variable [IsSepClosed K]

/-- A surviving fixed test yields a strict normalized extension over exactly the same field. -/
theorem nonzero_test_strict_normalized_extension
    (t : invariantCoordinates ρ) (ht : t ∈ tests) (hnt : w t.val ≠ 0) :
    ∃ v : Spec (.of K) ⟶ source p q (Option I) (some o),
      v ≫ first p q (Option I) (some o) = u ≫ first p q I o ∧
      (∀ i, v ≫ coordinate p q (Option I) (some o) (some i) =
        u ≫ coordinate p q I o i) ∧
      ∀ i, v ≫ coordinate p q (Option I) (some o) none ≠
        u ≫ coordinate p q I o i := by
  apply exists_strict_normalized_extension I o u
  intro hc
  exact hnt (complete_character_tests_vanish e I o U hU w hc t ht)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
