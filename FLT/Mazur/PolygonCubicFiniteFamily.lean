/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicGlobalGeneration

/-!
# A finite cubic coordinate family on the polygon

Retain the proved generating pair and add the three delta-coefficient sections
at every component: node value and the two branch-linear coefficients. The
family generates the actual line sheaf. Closed immersion is a separate claim.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints

/-- The two generators followed by three interpolation coordinates per component. -/
abbrev CubicIndex (n : ℕ) := ULift.{u} Bool ⊕ ULift.{u} (Fin n × Fin 3)

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- A single chosen coefficient on a single component. -/
def cubicDelta (i : Fin n) (k l : Fin 3) (j : Fin n) : K :=
  if j = i ∧ l = k then 1 else 0

/-- The actual finite family of cubic global sections used for projective coordinates. -/
def cubicFamily : CubicIndex.{u} n → Γ(polygonLine K n hn p q h a 3, ⊤)
  | .inl b => generatingPair K n hn p q h a b
  | .inr z => nodeSection K n hn p q h a
      (cubicDelta K n z.down.1 z.down.2 0)
      (cubicDelta K n z.down.1 z.down.2 1)
      (cubicDelta K n z.down.1 z.down.2 2)

/-- The original generating pair occurs unchanged in the coordinate family. -/
@[simp] lemma cubicFamily_inl (b : ULift.{u} Bool) :
    cubicFamily K n hn p q h a (.inl b) = generatingPair K n hn p q h a b := rfl

/-- Each interpolation coordinate has precisely its prescribed three lower coefficients. -/
lemma cubicFamily_coefficients (i j : Fin n) (k : Fin 3) :
    let P := ((sectionEquiv K n hn p q h a 2
      (cubicFamily K n hn p q h a (.inr ⟨(i, k)⟩))).val j).val
    P.coeff 0 = cubicDelta K n i k 0 j ∧
      P.coeff 1 = cubicDelta K n i k 1 j ∧
      P.coeff 2 = cubicDelta K n i k 2 j :=
  nodeSection_coefficients K n hn p q h a _ _ _ j

omit [NeZero n] in
/-- The coordinate index has exactly three coordinates per component and the generating pair. -/
lemma cubicIndex_card : Fintype.card (CubicIndex.{u} n) = 2 + n * 3 := by
  simp [CubicIndex]

/-- The enlarged family still generates the actual cubic line sheaf. -/
theorem cubicFamily_evaluation_epi :
    Epi (ProjectiveSpace.globalEvaluation (polygonLine K n hn p q h a 3)
      (cubicFamily K n hn p q h a)) where
  left_cancellation {N} f g hfg := by
    let := generatingPair_evaluation_epi K n hn p q h a
    apply (cancel_epi (ProjectiveSpace.globalEvaluation _
      (generatingPair K n hn p q h a))).mp
    apply N.freeHomEquiv.injective
    funext b
    rw [SheafOfModules.freeHomEquiv_comp_apply,
      SheafOfModules.freeHomEquiv_comp_apply]
    simp only [ProjectiveSpace.globalEvaluation, Equiv.apply_symm_apply]
    apply Subtype.ext
    funext U
    exact ProjectiveSpace.globalEvaluation_cancel (cubicFamily K n hn p q h a)
      f g hfg (.inl b) U.unop

end FLT.Mazur.PolygonCubicSections
