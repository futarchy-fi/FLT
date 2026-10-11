/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChartChange
public import FLT.Mazur.VariableHilbertEtaleRelation

/-!
# Affine translation neighborhoods preserve entire geometric Hilbert points

Refine the actual translation base at the translation coordinate of a given
field-valued Hilbert point. The full point factors through the refined chart,
so its original Picard class and its unrestricted Hilbert parameter survive.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  (g : Spec (.of K) ⟶ Spec (.of R)) (q : Over.mk g ⟶ variableHilbertTest f d V)

/-- An affine open in the actual translation base retains the whole original Hilbert point. -/
theorem exists_variableHilbert_affine_refinement :
    ∃ (E : Over (Spec (.of R))) (j : E ⟶ V)
      (p : Over.mk g ⟶ variableHilbertTest f d E),
      IsAffine E.left ∧ IsOpenImmersion j.left ∧ p ≫ baseMarkedChartChange f j d = q := by
  let v : Spec (.of K) ⟶ V.left := (q ≫ variableHilbertBase f d V).left
  obtain ⟨i, y, hy⟩ := V.left.affineCover.exists_eq (v default)
  let a := V.left.affineCover.f i
  have hr : Set.range v ⊆ Set.range a := by
    rintro _ ⟨z, rfl⟩
    exact ⟨y, hy.trans (congrArg v (Subsingleton.elim _ _))⟩
  let z := IsOpenImmersion.lift a v hr
  have hz : z ≫ a = v := IsOpenImmersion.lift_fac a v hr
  let E := Over.mk (a ≫ V.hom)
  let j : E ⟶ V := Over.homMk a
  let t : Over.mk g ⟶ E := Over.homMk z (by
    change z ≫ (a ≫ V.hom) = g
    rw [← Category.assoc, hz]
    exact (q ≫ variableHilbertBase f d V).w)
  let p := variableHilbertLift f d E t (q ≫ variableHilbertParameter f d V)
  refine ⟨E, j, p, inferInstanceAs (IsAffine (V.left.affineCover.X i)),
    inferInstanceAs (IsOpenImmersion (V.left.affineCover.f i)), ?_⟩
  apply prod.hom_ext
  · change p ≫ baseMarkedChartChange f j d ≫ variableHilbertBase f d V = _
    rw [baseMarkedChartChange_base, ← Category.assoc]
    rw [show p ≫ variableHilbertBase f d E = t from prod.lift_fst _ _]
    exact Over.OverMorphism.ext hz
  · change p ≫ baseMarkedChartChange f j d ≫ variableHilbertParameter f d V = _
    rw [baseMarkedChartChange_parameter]
    exact prod.lift_snd _ _

variable {L : X.Modules} (hL : AmpleLineBundle L)
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The same affine refinement preserves the original translated Picard class. -/
theorem exists_variableHilbert_affine_class_refinement [Etale V.hom] :
    ∃ (E : Over (Spec (.of R))) (j : E ⟶ V)
      (p : Over.mk g ⟶ variableHilbertTest f d E),
      IsAffine E.left ∧ IsOpenImmersion j.left ∧ Etale E.hom ∧
        p ≫ baseMarkedChartChange f j d = q ∧
        variableHilbertPoint f d hL E ((relativeFppfSheaf f).obj.map j.op c) _ p =
          variableHilbertPoint f d hL V c _ q := by
  obtain ⟨E, j, p, ha, hj, hp⟩ := exists_variableHilbert_affine_refinement f d V g q
  let _ := hj
  have he : Etale E.hom := by
    rw [← j.w]
    infer_instance
  refine ⟨E, j, p, ha, hj, he, hp, ?_⟩
  have h := baseMarkedChartChange_class f hL j (d, c) p
  dsimp only [baseMarkedIndexChange, Prod.fst, Prod.snd] at h
  rw [hp] at h
  exact h.symm

end FLT.Mazur.HilbertChart
