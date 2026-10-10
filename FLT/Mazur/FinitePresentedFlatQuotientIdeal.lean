/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatQuotientTrivialization
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Presenting ideals from finite presented flat quotients

The actual coefficient trivializations give presentations on a principal
cover of the ambient. Descent gives finite presentation of the entire ideal,
with no local or Noetherian assumption on either ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.FinitePresentation R B]

/-- A finitely presented flat quotient over the base presents the whole ambient ideal. -/
theorem ideal_finitePresentation_of_finitePresentation_flat_quotient
    (I : Ideal B) [Module.FinitePresentation R (B ⧸ I)] [Module.Flat R (B ⧸ I)] :
    Module.FinitePresentation B I := by
  classical
  let S : Set R := {r | Module.Free (Localization.Away r)
    ((Localization.Away r ⊗[R] B) ⧸
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := Localization.Away r)))}
  have hS : Ideal.span S = ⊤ := span_free_coefficient_quotient_away (R := R) I
  let s : Set B := algebraMap R B '' S
  have hs : Ideal.span s = ⊤ := by
    rw [show s = algebraMap R B '' S from rfl, ← Ideal.map_span, hS, Ideal.map_top]
  have hex (g : s) : ∃ r ∈ S, algebraMap R B r = g.1 := g.2
  choose r hr he using hex
  let T (g : s) := Localization.Away (r g) ⊗[R] B
  let _ (g : s) : IsLocalization.Away g.1 (T g) := by
    rw [← he g]
    change IsLocalization.Away (algebraMap R B (r g))
      (Localization.Away (r g) ⊗[R] B)
    infer_instance
  apply Module.FinitePresentation.of_localizationSpan' s hs
    (Rₚ := T) (Mₚ := fun g ↦ ↥(I.map (algebraMap B (T g))))
    (fun g ↦ Algebra.idealMap (T g) I)
  intro g
  let _ : Module.Free (Localization.Away (r g))
      (T g ⧸ I.map (algebraMap B (T g))) := hr g
  let _ : Module.Finite (Localization.Away (r g))
      (T g ⧸ I.map (algebraMap B (T g))) :=
    finite_coefficient_ideal_quotient (R := R) (S := Localization.Away (r g)) I
  cases subsingleton_or_nontrivial (Localization.Away (r g))
  · let _ := Module.subsingleton (Localization.Away (r g)) (T g)
    let _ : Subsingleton ↥(I.map (algebraMap B (T g))) := inferInstance
    exact Module.FinitePresentation.of_subsingleton (R := T g)
      ↥(I.map (algebraMap B (T g)))
  · exact ideal_finitePresentation_of_quotient_basis _
      (Module.finBasis (Localization.Away (r g)) _)

end FLT.Mazur.FCurve
