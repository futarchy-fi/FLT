/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleDenseFiniteGround
public import FLT.Mazur.CommonGroundEnvelopeSquare

/-!
# Original envelope interiors over a constructed dense coefficient open

One principal coefficient open, depending only on the affine etale
translation, works for EVERY original source and envelope open. All full
fibers above it are actual original interior points. In particular every
remaining specialization obstruction lies above its proper closed complement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleDenseFiniteGround
open SchemeOpenEnvelope CommonGroundEnvelope
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R] [IsDomain R]
  (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
local notation "q" => groundMap R V

/-- The dense open lives in the unchanged coefficient scheme. -/
def groundOpen : (Spec (.of R)).Opens := (q).opensRange

theorem groundOpen_dense : Dense (groundOpen R V : Set (Spec (.of R))) :=
  (q).denseRange

variable (A : Over (Spec (.of R)))
local notation "B" => changed q A
local notation "W" => changed q V
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "π₀" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- The whole independent envelope has finite projection on the dense coefficient open. -/
theorem envelope_isFinite : IsFinite π := by
  let _ : IsFinite (W).hom := translation_isFinite R V
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd B W)).flip inferInstance

variable (O : (prod A V).left.Opens)

/-- All original full fibers over the constructed coefficient open are original interior points. -/
theorem original_interior_of_mem_groundOpen (x : A.left)
    (hx : x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O)
    (hb : A.hom x ∈ groundOpen R V) :
    x ∈ SchemeOpenEnvelope.fullFiberInterior π₀ O := by
  obtain ⟨s, hs⟩ := hb
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback A.hom q) x s hs.symm
  have hf : y ∈ SchemeOpenEnvelope.fullFiberLocus π (comparison q A V ⁻¹ᵁ O) := by
    rw [CommonGroundEnvelope.fullFiberLocus]
    change pullback.fst A.hom q y ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O
    rwa [hy]
  let _ := envelope_isFinite R V A
  have hi : y ∈ fullFiberInterior π (comparison q A V ⁻¹ᵁ O) := by
    rw [fullFiberInterior_eq_fullFiberOpen π _ (π).isClosedMap]
    exact hf
  rw [CommonGroundEnvelope.fullFiberInterior] at hi
  change pullback.fst A.hom q y ∈ SchemeOpenEnvelope.fullFiberInterior π₀ O at hi
  rwa [hy] at hi

/-- This is uniform over all full source points, including nongeneric coefficient points. -/
theorem original_interior_iff_over_groundOpen (x : A.left)
    (hb : A.hom x ∈ groundOpen R V) :
    x ∈ SchemeOpenEnvelope.fullFiberInterior π₀ O ↔
      x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O :=
  ⟨fun h ↦ interior_subset h, fun h ↦ original_interior_of_mem_groundOpen R V A O x h hb⟩

/-- Every excluded specialization obstruction is supported over a proper closed coefficient set. -/
theorem excluded_specialization_not_mem_groundOpen (x : A.left)
    (hx : x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O)
    (e : (prod A V).left) (he : e ∉ O) (hs : π₀ e ⤳ x) :
    A.hom x ∉ groundOpen R V := by
  intro hb
  have hi := original_interior_of_mem_groundOpen R V A O x hx hb
  have hf : π₀ e ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O :=
    interior_subset (hs.mem_open (fullFiberInterior π₀ O).isOpen hi)
  exact he ((mem_fullFiberLocus π₀ O (π₀ e)).mp hf e rfl)

end FLT.Mazur.AffineEtaleDenseFiniteGround
