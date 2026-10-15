/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonGroundEnvelopeSquare
public import FLT.Mazur.ProperCoreGroundInterior
public import FLT.Mazur.TranslationProperCore

/-!
# Proper cores inside the full common-ground envelope

An actual translation core gives a proper independent envelope core. Its
residual image is measured in the changed source, while its closure detects
the ORIGINAL interior. Whole-fiber coverage only excludes the residual image
at the retained point; closure avoidance is kept as a separate condition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CommonGroundEnvelope
open SchemeOpenEnvelope ProperCoreResidualInterior
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S U : Scheme.{u}} (q : U ⟶ S) (A V : Over S)
local notation "B" => changed q A
local notation "W" => changed q V
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "ρ" => Over.Hom.left (prod.snd : prod B W ⟶ W)
local notation "π₀" => Over.Hom.left (prod.fst : prod A V ⟶ A)
variable (T : (pullback V.hom q).Opens)

/-- The actual open independent core inside the whole changed envelope. -/
def envelopeCore : (prod B W).left.Opens := TranslationProperCore.core B W T

instance envelopeCore_projection_isFinite [IsFinite (T.ι ≫ pullback.snd V.hom q)] :
    IsFinite ((envelopeCore q A V T).ι ≫ π) := by
  let _ : IsFinite (T.ι ≫ (W).hom) := inferInstanceAs
    (IsFinite (T.ι ≫ pullback.snd V.hom q))
  exact TranslationProperCore.core_projection_isFinite B W T

instance envelopeCore_projection_isProper [IsProper (T.ι ≫ pullback.snd V.hom q)] :
    IsProper ((envelopeCore q A V T).ι ≫ π) := by
  let _ : IsProper (T.ι ≫ (W).hom) := inferInstanceAs
    (IsProper (T.ι ≫ pullback.snd V.hom q))
  exact TranslationProperCore.core_projection_isProper B W T

/-- A clopen translation core stays clopen in the entire independent envelope. -/
theorem envelopeCore_isClosed (hT : IsClosed (T : Set (pullback V.hom q : Scheme))) :
    IsClosed (envelopeCore q A V T : Set (prod B W).left) := hT.preimage (ρ).continuous

variable (O : (prod A V).left.Opens)

/-- Excluded residual coordinates, with the original envelope open pulled back exactly. -/
def residualImage : Set (B).left :=
  residualBadImage π (comparison q A V ⁻¹ᵁ O) (envelopeCore q A V T)

/-- All independent points outside both the original open and the translation core are kept. -/
theorem residualImage_eq :
    residualImage q A V T O = π '' {e : (prod B W).left |
      comparison q A V e ∉ O ∧ ρ e ∉ T} := rfl

/-- Whole translation-fiber coverage retains every independent envelope point over the source. -/
theorem fiber_subset_envelopeCore (u : U)
    (hT : ∀ w : (pullback V.hom q : Scheme), pullback.snd V.hom q w = u → w ∈ T)
    (x : (B).left) (hx : pullback.snd A.hom q x = u) :
    ∀ e : (prod B W).left, π e = x → e ∈ envelopeCore q A V T :=
  TranslationProperCore.fiber_subset_core B W T u hT x hx

/-- Coverage excludes actual residual image points, without asserting closure avoidance. -/
theorem not_mem_residualImage (u : U)
    (hT : ∀ w : (pullback V.hom q : Scheme), pullback.snd V.hom q w = u → w ∈ T)
    (x : (B).left) (hx : pullback.snd A.hom q x = u) :
    x ∉ residualImage q A V T O := by
  rintro ⟨e, he, hex⟩
  exact he.2 (fiber_subset_envelopeCore q A V T u hT x hx e hex)

variable [IsProper (T.ι ≫ pullback.snd V.hom q)] [Etale q]

/-- At a full original fiber, closure avoidance is exactly original interior membership. -/
theorem original_interior_iff (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O) :
    pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberInterior π₀ O ↔
      x ∉ closure (residualImage q A V T O) :=
  ProperCoreGroundInterior.original_mem_iff (isPullback q A V) O
    (envelopeCore q A V T) (pullback.fst A.hom q).isOpenMap x hx

/-- Closedness of the actual residual image suffices on every reached original full fiber. -/
theorem original_interior_of_closed_residual
    (hr : IsClosed (residualImage q A V T O)) (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O) :
    pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberInterior π₀ O :=
  ProperCoreGroundInterior.original_mem_of_closed_residual (isPullback q A V) O
    (envelopeCore q A V T) (pullback.fst A.hom q).isOpenMap hr _ hx ⟨x, rfl⟩

end FLT.Mazur.CommonGroundEnvelope
