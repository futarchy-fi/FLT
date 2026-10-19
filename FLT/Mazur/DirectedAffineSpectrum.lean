/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Spectrum coordinates on the directed affine open cover

The coordinate rings and restriction homomorphisms retain the actual open
inclusions. Their strict laws permit concrete affine constructions to glue.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.DirectedAffineSpectrum
universe u
variable (X : Scheme.{u})

/-- Coordinate ring of an actual affine open, as a scheme. -/
abbrev Ring (U : X.affineOpens) := Γ(U.1.toScheme, ⊤)

/-- Spectrum coordinates on an actual affine open. -/
def chart (U : X.affineOpens) : Spec (Ring X U) ⟶ X :=
  U.1.toScheme.isoSpec.inv ≫ U.1.ι

/-- Restriction of functions along the actual open inclusion. -/
def restriction {U V : X.affineOpens} (h : U ≤ V) : Ring X V →+* Ring X U :=
  (X.homOfLE h).appTop.hom

/-- The coordinate restriction retains the inclusion into the original scheme. -/
@[reassoc] theorem restriction_chart {U V : X.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (restriction X h)) ≫ chart X V = chart X U := by
  unfold restriction chart
  change Spec.map (X.homOfLE h).appTop ≫ _ = _
  rw [Scheme.isoSpec_inv_naturality_assoc, Scheme.homOfLE_ι]

/-- Restricting to the same open is the identity homomorphism. -/
theorem restriction_id (U : X.affineOpens) :
    restriction X (le_refl U) = RingHom.id (Ring X U) := by
  unfold restriction
  have h : X.homOfLE (show U.1 ≤ U.1 from le_rfl) = 𝟙 U.1.toScheme := by
    rw [← cancel_mono U.1.ι, Scheme.homOfLE_ι, Category.id_comp]
  rw [h]
  rfl

/-- Function restrictions compose in the order required by comparison refinements. -/
theorem restriction_comp {U V W : X.affineOpens} (h : U ≤ V) (k : V ≤ W) :
    restriction X (h.trans k) = (restriction X h).comp (restriction X k) := by
  unfold restriction
  rw [← Scheme.homOfLE_homOfLE X h k, Scheme.Hom.comp_appTop]
  rfl

/-- A cartesian coordinate square remains cartesian over the actual affine opens. -/
theorem isPullback_toOpen {U V : X.affineOpens} (h : U ≤ V)
    {P Q : Scheme.{u}} (s : P ⟶ Spec (Ring X U)) (t : Q ⟶ Spec (Ring X V))
    (m : P ⟶ Q)
    (hp : IsPullback s m (Spec.map (CommRingCat.ofHom (restriction X h))) t) :
    IsPullback (s ≫ U.1.toScheme.isoSpec.inv) m (X.homOfLE h)
      (t ≫ V.1.toScheme.isoSpec.inv) := by
  apply hp.paste_horiz
  apply IsPullback.of_horiz_isIso
  exact ⟨(Scheme.isoSpec_inv_naturality (X.homOfLE h)).symm⟩

end FLT.Mazur.DirectedAffineSpectrum
