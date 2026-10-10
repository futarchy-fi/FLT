/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveLargeDegreeVanishing
public import FLT.Mazur.ProperCohomologyFieldVanishing

/-!
# A degree bound uniform over field extensions

An acyclic line on the original curve stays acyclic after every extension
of fields. Its degree and the structure Euler characteristic are unchanged.
Consequently the same bound works for every line on each integral curve
obtained by field extension, including lines that do not descend.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleSheafTensorAssociator

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim X = 1) (hc : HasConstantGlobalSections f)

/-- One acyclic line controls all lines on every integral field extension of the curve. -/
theorem curve_field_h1_vanishing_of_acyclic_line {A : X.Modules}
    (hA : LocallyFreeRankOne A) [Subsingleton (ModuleScalarH f A 1)]
    {K : Type} [Field K] {P : Scheme} [IsIntegral P]
    {p : P ⟶ X} {q : P ⟶ Spec (.of K)} {g : Spec (.of K) ⟶ Spec (.of k)}
    (h : IsPullback p q f g) (hdP : topologicalKrullDim P ≤ 1)
    {L : P.Modules} (hL : LocallyFreeRankOne L)
    (hdeg : curveSheafDegree f A + curveGenus f hd hc ≤ curveSheafDegree q L) :
    Subsingleton (ModuleScalarH q L 1) := by
  have : IsProper q := MorphismProperty.of_isPullback h inferInstance
  have := hA.isFinitePresentation
  let B := (pullback p).obj A
  have hB : LocallyFreeRankOne B := hA.pullback p
  have : Subsingleton (ModuleScalarH q B 1) :=
    (proper_line_cohomology_field_vanishing_iff h hA 1).mpr inferInstance
  have hdual : curveSheafDegree q (moduleSheafDual B) = -curveSheafDegree q B :=
    SchemePicard.degree_inv q hdP (SchemePicard.mk B hB)
  have hBdeg : curveSheafDegree q B = curveSheafDegree f A :=
    curveSheafDegree_field_baseChange h A
  have he : curveEulerCharacteristic q (structureUnitModule P) =
      1 - curveGenus f hd hc :=
    (structure_euler_field_baseChange h).trans
      (curveEulerCharacteristic_structure_eq_one_sub_genus f hd hc)
  let N := tensor (moduleSheafDual B) L
  have hNdeg : curveSheafDegree q N = curveSheafDegree q L - curveSheafDegree f A := by
    rw [curveSheafDegree_line_tensor q hdP hL hB.dual, hdual, hBdeg]
    omega
  have hpos : 0 < Module.finrank K (ModuleScalarH q N 0) := by
    change curveEulerCharacteristic q N - curveEulerCharacteristic q (structureUnitModule P) =
      curveSheafDegree q L - curveSheafDegree f A at hNdeg
    rw [he] at hNdeg
    unfold curveEulerCharacteristic at hNdeg
    omega
  obtain ⟨s, hs⟩ := exists_nonzero_section_of_h0_pos q N hpos
  have hz := LineSectionTwistSystem.tensor_cohomology_vanishing_of_section q hdP
    hB (hB.dual.tensor hL) s hs 1 (by decide)
  let e : tensor B N ≅ L := (associator B (moduleSheafDual B) L).symm ≪≫
    congr (comm B (moduleSheafDual B) ≪≫ lineSheafDualEvaluationIso hB) (Iso.refl L) ≪≫
      leftUnitor L
  let c : ModuleScalarH q (tensor B N) 1 ≃ₗ[K] ModuleScalarH q L 1 :=
    ((moduleScalarHFunctor q 1).mapIso e).toLinearEquiv
  exact c.symm.injective.subsingleton

include hd hc in
/-- The degree bound is chosen before the extension field and the new line bundle. -/
theorem exists_uniform_field_degree_bound {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ d : ℤ, ∀ (K : Type) [Field K] (P : Scheme) [IsIntegral P]
      (p : P ⟶ X) (q : P ⟶ Spec (.of K)) (g : Spec (.of K) ⟶ Spec (.of k)),
      IsPullback p q f g → topologicalKrullDim P ≤ 1 →
      ∀ L : P.Modules, LocallyFreeRankOne L → d ≤ curveSheafDegree q L →
        Subsingleton (ModuleScalarH q L 1) := by
  obtain ⟨A, hA, hz⟩ := exists_acyclic_line_of_ample f hB
  refine ⟨curveSheafDegree f A + curveGenus f hd hc, ?_⟩
  intro K _ P _ p q g h hdP L hL hdeg
  exact curve_field_h1_vanishing_of_acyclic_line f hd hc hA h hdP hL hdeg

/-- The section dimension after field extension uses the genus of the original curve. -/
theorem curve_field_h0_eq_of_h1_vanishing {K : Type} [Field K] {P : Scheme}
    {p : P ⟶ X} {q : P ⟶ Spec (.of K)} {g : Spec (.of K) ⟶ Spec (.of k)}
    (h : IsPullback p q f g) (L : P.Modules) [Subsingleton (ModuleScalarH q L 1)] :
    (Module.finrank K (ModuleScalarH q L 0) : ℤ) =
      curveSheafDegree q L + 1 - curveGenus f hd hc := by
  have he := (structure_euler_field_baseChange h).trans
    (curveEulerCharacteristic_structure_eq_one_sub_genus f hd hc)
  change _ = (curveEulerCharacteristic q L -
    curveEulerCharacteristic q (structureUnitModule P)) + 1 - curveGenus f hd hc
  rw [he, curveEulerCharacteristic,
    Module.finrank_zero_of_subsingleton (R := K) (M := ModuleScalarH q L 1),
    Nat.cast_zero, sub_zero]
  omega

end FLT.Mazur.FCurve
