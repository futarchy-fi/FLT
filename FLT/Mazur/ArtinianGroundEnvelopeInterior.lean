/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonGroundEnvelopeSquare
public import FLT.Mazur.QuasiCompactEtaleGeometricSections

/-!
# Full original envelopes on locally Artinian ground

A quasi-compact etale translation over a locally Artinian scheme is finite.
Consequently the full independent envelope projection is closed, for every
source and every envelope open. This includes nonreduced Artinian ground.
An arbitrary change to Artinian ground gives fiberwise openness; recovering
an ORIGINAL interior additionally requires the source comparison to be open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.ArtinianGroundEnvelope
open SchemeOpenEnvelope CommonGroundEnvelope
universe u
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} (A V : Over S) [Etale V.hom] [QuasiCompact V.hom]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- Finiteness is a consequence of the actual ground, not a supplied translation condition. -/
theorem translation_isFinite [IsLocallyArtinian S] : IsFinite V.hom := by
  let _ := QuasiCompactEtaleGeometricSections.locallyQuasiFinite V.hom
  exact IsFinite.of_locallyQuasiFinite V.hom

/-- The entire independent envelope, including every residual branch, has finite projection. -/
theorem projection_isFinite [IsLocallyArtinian S] : IsFinite π := by
  let _ := translation_isFinite V
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip inferInstance

/-- Every full original fiber has a neighborhood of full fibers over Artinian ground. -/
theorem interior_coe [IsLocallyArtinian S] (O : (prod A V).left.Opens) :
    (fullFiberInterior π O : Set A.left) = fullFiberLocus π O := by
  let _ := projection_isFinite A V
  rw [fullFiberInterior_eq_fullFiberOpen π O (π).isClosedMap]
  rfl

variable {U : Scheme.{u}} (q : U ⟶ S) [IsLocallyArtinian U]
local notation "B" => changed q A
local notation "W" => changed q V
local notation "π'" => Over.Hom.left (prod.fst : prod B W ⟶ B)

/-- Artinian base change opens the full original fiber locus on the changed source. -/
theorem changed_interior_coe (O : (prod A V).left.Opens) :
    (fullFiberInterior π' (comparison q A V ⁻¹ᵁ O) : Set (B).left) =
      pullback.fst A.hom q ⁻¹' fullFiberLocus π O := by
  let _ : Etale (W).hom := inferInstanceAs (Etale (pullback.snd V.hom q))
  let _ : QuasiCompact (W).hom := inferInstanceAs (QuasiCompact (pullback.snd V.hom q))
  rw [interior_coe B W, CommonGroundEnvelope.fullFiberLocus]

/-- An OPEN comparison upgrades the Artinian fiber statement to an original neighborhood. -/
theorem original_interior_of_open_comparison (O : (prod A V).left.Opens)
    (hq : IsOpenMap (pullback.fst A.hom q)) (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ fullFiberLocus π O) :
    pullback.fst A.hom q x ∈ fullFiberInterior π O := by
  have hi : x ∈ fullFiberInterior π' (comparison q A V ⁻¹ᵁ O) := by
    rw [← SetLike.mem_coe, changed_interior_coe A V q O]
    exact hx
  rw [fullFiberInterior_baseChange (CommonGroundEnvelope.isPullback q A V) O hq] at hi
  exact hi

end FLT.Mazur.ArtinianGroundEnvelope
