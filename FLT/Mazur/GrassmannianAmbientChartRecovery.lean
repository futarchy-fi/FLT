/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientClassifyingNaturality

/-!
# Recovering original quotients from equal glued chart morphisms

The actual pullback of two chart opens factors any equality through the determinant
intersection. Its affine algebra map recovers equality of the full original quotients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Equality in the glued scheme recovers the entire original ambient quotient. -/
theorem ambientGluedChartPoint_eq_iff (i j : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i))
    (P : AmbientChartPoint (ambientChartBaseChange A j)) :
    ambientGluedChartPoint i N = ambientGluedChartPoint j P ↔ N.val = P.val := by
  refine ⟨fun h ↦ ?_, ambientGluedChartPoint_eq i j N P⟩
  let n := (ambientChartSchemePointEquiv i).symm N
  let p := (ambientChartSchemePointEquiv j).symm P
  let H := ambientGrassmannianChart_isPullback R M κ d i j
  let t := H.lift n.val p.val h
  have ht : t ≫ Spec.algebraMap R (ambientOverlapRing (ambientChartChange i j)) =
      Spec.algebraMap R A := by
    rw [← (ambientOverlapFirstPoint i j).property]
    change t ≫ indexedOverlapInclusion i j ≫ splitChartStructure R κ d = _
    rw [← Category.assoc, show t ≫ indexedOverlapInclusion i j = n.val from
      H.lift_fst _ _ h]
    exact n.property
  let a := affineOverAlgHom R (ambientOverlapRing (ambientChartChange i j)) A t ht
  have ha : Spec.map (CommRingCat.ofHom a.toRingHom) = t :=
    affineOverAlgHom_spec R _ A t ht
  have hn : splitChartSchemePointMap a (ambientOverlapFirstPoint i j) = n := by
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ indexedOverlapInclusion i j = _
    rw [ha]
    exact H.lift_fst _ _ h
  have hp : splitChartSchemePointMap a (ambientOverlapSecondPoint i j) = p := by
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ indexedChartTransition i j = _
    rw [ha]
    exact H.lift_snd _ _ h
  have he := ambientOverlap_classifications_test_eq i j a
  rw [hn, hp] at he
  exact (congrArg Subtype.val ((ambientChartSchemePointEquiv i).apply_symm_apply N)).symm.trans
    (he.symm.trans (congrArg Subtype.val
      ((ambientChartSchemePointEquiv j).apply_symm_apply P)))

/-- Each chart classification remains injective after passage to the glued scheme. -/
theorem ambientGluedChartPoint_injective (i : AmbientChartIndex R M κ d) :
    Function.Injective (ambientGluedChartPoint (A := A) i) := by
  intro N P h
  exact Subtype.ext ((ambientGluedChartPoint_eq_iff i i N P).mp h)

end FLT.Mazur.GrassmannianChart
