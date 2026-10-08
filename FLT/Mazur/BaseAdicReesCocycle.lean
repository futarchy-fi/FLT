/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesRestriction

/-!
# Identity and composition of actual relative Rees restrictions

The ring and module restrictions use the original presheaf maps, so their
identity and triple-overlap laws hold coefficient by coefficient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) {U V W : X.affineOpens}

/-- The scalar restriction fixes each original chart element. -/
lemma chartRingRestriction_id :
    let _ := chartAlgebra f U
    chartRingRestriction f (U := U) le_rfl = AlgHom.id R Γ(X, U.1) := by
  let _ := chartAlgebra f U
  ext r
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (.op U.1)) r

/-- Chart scalar restrictions compose along the original inclusions. -/
lemma chartRingRestriction_comp (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    let _ := chartAlgebra f U
    let _ := chartAlgebra f V
    let _ := chartAlgebra f W
    (chartRingRestriction f h).comp (chartRingRestriction f k) =
      chartRingRestriction f (h.trans k) := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f V
  let _ := chartAlgebra f W
  ext r
  exact (ConcreteCategory.congr_hom
    (X.presheaf.map_comp (homOfLE k).op (homOfLE h).op) r).symm

/-- The full relative tensor ring restriction is the identity on a repeated chart. -/
lemma relativeRingRestriction_id :
    let _ := chartAlgebra f U
    relativeRingRestriction f J (U := U) le_rfl = AlgHom.id R _ := by
  let _ := chartAlgebra f U
  change Rees.relativeAlgebraMap J _ = _
  rw [chartRingRestriction_id, Rees.relativeAlgebraMap_id]

/-- The relative tensor maps satisfy the triple-overlap composition law. -/
lemma relativeRingRestriction_comp (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    let _ := chartAlgebra f U
    let _ := chartAlgebra f V
    let _ := chartAlgebra f W
    (relativeRingRestriction f J h).comp (relativeRingRestriction f J k) =
      relativeRingRestriction f J (h.trans k) := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f V
  let _ := chartAlgebra f W
  change (Rees.relativeAlgebraMap J _).comp (Rees.relativeAlgebraMap J _) = _
  rw [Rees.relativeAlgebraMap_comp, chartRingRestriction_comp]
  rfl

variable (M : X.Modules)

/-- Identity restriction retains every polynomial coefficient of the relative model. -/
lemma relativeRestriction_id (s : let _ := chartAlgebra f U
    Rees.extendedModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J) :
    relativeRestriction f J M le_rfl s = s := by
  apply Subtype.ext
  ext n
  exact ConcreteCategory.congr_hom (M.presheaf.map_id (.op U.1)) (s.val.coeff n)

/-- The actual relative power modules satisfy the triple-overlap composition law. -/
lemma relativeRestriction_comp (h : U.1 ≤ V.1) (k : V.1 ≤ W.1)
    (s : let _ := chartAlgebra f W
      Rees.extendedModule (S := Γ(X, W.1)) (M := Γ(M, W.1)) J) :
    relativeRestriction f J M h (relativeRestriction f J M k s) =
      relativeRestriction f J M (h.trans k) s := by
  apply Subtype.ext
  ext n
  exact (ConcreteCategory.congr_hom
    (M.presheaf.map_comp (homOfLE k).op (homOfLE h).op) (s.val.coeff n)).symm

end FLT.Mazur.BaseAdicRees
