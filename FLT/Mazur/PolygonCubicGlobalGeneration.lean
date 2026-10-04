/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusGenerator
public import FLT.Mazur.ModuleGlobalGeneration

/-!
# Sheaf-level global generation of the polygon cubic

The canonical divisor section and the uniform interior-X section generate the
actual cubic divisor line. The evaluation from the free sheaf on these two
sections is epi. This does not yet construct a projective embedding.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The canonical section and the uniform first interior section of the cubic line. -/
def generatingPair (b : ULift.{u} Bool) : Γ(polygonLine K n hn p q h a 3, ⊤) :=
  match b.down with
  | false => divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow 3) ⊤
  | true => nodeSection K n hn p q h a 0 1 0

/-- The genuine cubic global sections generate the polygon line as a sheaf. -/
theorem generatingPair_evaluation_epi :
    Epi (ProjectiveSpace.globalEvaluation (polygonLine K n hn p q h a 3)
      (generatingPair K n hn p q h a)) := by
  let U : Option (Fin n) → C.left.Opens
    | none => divisorComplement K n p a
    | some i => torusOpen K n hn p q h i
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ (PolygonBoundaryDivisor.ideal K n p a).support
    · obtain ⟨i, hi⟩ := support_mem_torusOpen K n hn p q h a x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨some i, hi⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨none, hx⟩
  apply globalEvaluation_epi_of_sectionHom_isIso (generatingPair K n hn p q h a)
    U hU (fun i ↦ ULift.up i.isSome)
  intro i
  cases i with
  | none =>
    change IsIso (sectionHom _ (divisorComplement K n p a)
      ((polygonLine K n hn p q h a 3).presheaf.map (homOfLE le_top).op
        (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow 3) ⊤)))
    rw [divisorSection_restrict]
    exact canonicalSection_isIso_complement K n hn p q h a
  | some i => exact interiorSection_isIso_torusOpen K n hn p q h a i

end FLT.Mazur.PolygonCubicSections
