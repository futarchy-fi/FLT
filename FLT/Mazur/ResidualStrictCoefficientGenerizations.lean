/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EnvelopeVerticalGenerizations
public import FLT.Mazur.CommonGroundResidualGenerizations

/-!
# Residual obstruction requires a strict original coefficient specialization

Apply fiberwise openness to the original independent envelope, before any
change of ground. Every residual generic witness that accumulates at an
original full fiber must change the ORIGINAL coefficient point strictly.
This removes all vertical witnesses from the finite W312 obstruction test.
It does not rule out strict coefficient generizations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CommonGroundEnvelope
open SchemeOpenEnvelope
universe u
set_option backward.isDefEq.respectTransparency false
variable {S U : Scheme.{u}} (q : U ⟶ S) (A V : Over S)
  [Etale V.hom] [QuasiCompact V.hom]
local notation "B" => changed q A
local notation "W" => changed q V
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "π₀" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "a" => pullback.fst A.hom q ≫ A.hom
variable (O : (prod A V).left.Opens)

/-- Any excluded witness forces a strict specialization on the unchanged coefficient scheme. -/
theorem excluded_specialization_original_coefficient (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O)
    (e : (prod B W).left) (he : comparison q A V e ∉ O) (hs : π e ⤳ x) :
    a (π e) ⤳ a x ∧ a (π e) ≠ a x := by
  have hp : π₀ (comparison q A V e) = pullback.fst A.hom q (π e) :=
    congrArg (fun g : (prod B W).left ⟶ A.left ↦ g e) (comparison_fst q A V)
  have hspec : π₀ (comparison q A V e) ⤳ pullback.fst A.hom q x := by
    rw [hp]
    exact hs.map (pullback.fst A.hom q).continuous
  refine ⟨hs.map (a).continuous, ?_⟩
  have hne := EnvelopeVerticalGenerizations.excluded_specialization_base_ne A V O
    hx (comparison q A V e) he hspec
  rwa [hp] at hne

variable [IsAffine S] [IsAffine U] [IsAffine A.left] [IsAffine V.left]
  [Etale q] [IsLocallyNoetherian A.left] (T : (pullback V.hom q).Opens)
  [IsProper (T.ι ≫ pullback.snd V.hom q)]

/-- A finite residual test in which every contributing witness changes the original coefficient. -/
theorem exists_finite_strictCoefficient_test :
    ∃ F : Set (prod B W).left, F.Finite ∧
      (∀ e ∈ F, comparison q A V e ∉ O ∧ e ∉ envelopeCore q A V T) ∧
      ∀ x : (B).left, pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O →
        (pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberInterior π₀ O ↔
          ∀ e ∈ F, ¬ π e ⤳ x) ∧
        (∀ e ∈ F, π e ⤳ x → a (π e) ⤳ a x ∧ a (π e) ≠ a x) := by
  obtain ⟨F, hF, hFO, ht⟩ := exists_finite_originalInterior_test q A V T O
  refine ⟨F, hF, hFO, fun x hx ↦ ⟨ht x hx, ?_⟩⟩
  intro e he hs
  exact excluded_specialization_original_coefficient q A V O x hx e (hFO e he).1 hs

end FLT.Mazur.CommonGroundEnvelope
