/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonGroundEnvelopeCore
public import FLT.Mazur.ProperCoreResidualGenerizations

/-!
# Finite original-interior tests on the constructed common ground

Affine etale common-ground envelopes over locally Noetherian original sources
are Noetherian. Finitely many actual excluded residual points therefore test
the original full interior simultaneously at every reached original full fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CommonGroundEnvelope
open SchemeOpenEnvelope ProperCoreResidualInterior
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S U : Scheme.{u}} (q : U ⟶ S) (A V : Over S)
  [IsAffine S] [IsAffine U] [IsAffine A.left] [IsAffine V.left]
  [Etale q] [Etale V.hom] [IsLocallyNoetherian A.left]
local notation "B" => changed q A
local notation "W" => changed q V
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "π₀" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- Noetherianity belongs to the full ambient envelope, including its residual coordinates. -/
theorem envelope_noetherianSpace : NoetherianSpace (prod B W).left := by
  let _ : IsAffine (B).left := inferInstanceAs (IsAffine (pullback A.hom q))
  let _ : IsAffine (W).left := inferInstanceAs (IsAffine (pullback V.hom q))
  let _ : IsAffine (prod B W).left := IsAffine.of_isIso (Over.prodLeftIsoPullback B W).hom
  let _ : IsLocallyNoetherian (B).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst A.hom q)
  let _ : Etale (W).hom := inferInstanceAs (Etale (pullback.snd V.hom q))
  let _ : Etale π := MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd B W)).flip
    (inferInstanceAs (Etale (W).hom))
  let _ := LocallyOfFiniteType.isLocallyNoetherian π
  let _ : IsNoetherian (prod B W).left := ⟨⟩
  infer_instance

variable (T : (pullback V.hom q).Opens) (O : (prod A V).left.Opens)

/-- A finite actual residual family controls the whole residual image closure. -/
theorem exists_finite_residual_test :
    ∃ F : Set (prod B W).left, F.Finite ∧
      (∀ e ∈ F, comparison q A V e ∉ O ∧ e ∉ envelopeCore q A V T) ∧
      ∀ x : (B).left, x ∈ closure (residualImage q A V T O) ↔
        ∃ e ∈ F, π e ⤳ x := by
  let _ := envelope_noetherianSpace q A V
  exact exists_finite_residual_generizations π (comparison q A V ⁻¹ᵁ O)
    (envelopeCore q A V T)

variable [IsProper (T.ι ≫ pullback.snd V.hom q)]

/-- The finite residual family tests the ORIGINAL full interior at every full lifted fiber. -/
theorem exists_finite_originalInterior_test :
    ∃ F : Set (prod B W).left, F.Finite ∧
      (∀ e ∈ F, comparison q A V e ∉ O ∧ e ∉ envelopeCore q A V T) ∧
      ∀ x : (B).left, pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O →
        (pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberInterior π₀ O ↔
          ∀ e ∈ F, ¬ π e ⤳ x) := by
  obtain ⟨F, hF, hFO, ht⟩ := exists_finite_residual_test q A V T O
  refine ⟨F, hF, hFO, fun x hx ↦ ?_⟩
  rw [original_interior_iff q A V T O x hx, ht x]
  simp only [not_exists, not_and]

/-- Residual coordinates over all generizations suffice; no closure hypothesis is needed. -/
theorem originalInterior_iff_residual_generizations (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O) :
    pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberInterior π₀ O ↔
      ∀ e : (prod B W).left, π e ⤳ x → e ∉ envelopeCore q A V T →
        comparison q A V e ∈ O := by
  let _ := envelope_noetherianSpace q A V
  rw [original_interior_iff q A V T O x hx]
  change (x ∉ closure (residualBadImage π (comparison q A V ⁻¹ᵁ O)
    (envelopeCore q A V T))) ↔ _
  rw [mem_closure_residual_iff]
  constructor
  · intro h e he ht
    by_contra ho
    exact h ⟨e, ⟨ho, ht⟩, he⟩
  · rintro h ⟨e, ⟨ho, ht⟩, he⟩
    exact ho (h e he ht)

end FLT.Mazur.CommonGroundEnvelope
