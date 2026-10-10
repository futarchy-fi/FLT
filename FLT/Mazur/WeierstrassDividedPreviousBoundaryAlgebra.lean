/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBoundary

/-!
# The full algebra transition for the actual preceding boundary

Compose the parameter identification with the horizontal contraction
isomorphism. The resulting map agrees with the integral contraction on
every function, and its spectrum is the actual preceding boundary map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
open WeierstrassSuccessiveX
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "B" => Coordinate W (π ^ k) π e.b3 e.b4 e.b6
local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "u" => coord W (π ^ k) π e.b3 e.b4 e.b6 2
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ k) (π ^ k)
  d.b3 d.b4 d.b6 (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)

/-- The parameter-corrected full integral horizontal transition. -/
def previousBoundaryEquiv : Localization.Away x ≃ₐ[R] Localization.Away u :=
  (WeierstrassDilatation.horizontalParameterEquiv W (π ^ k) (π ^ k)
    d.b3 d.b4 d.b6 (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
    (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)).trans
      (horizontalEquiv W (π ^ k) π e.b3 e.b4 e.b6)

/-- Localization of equal parameters retains every original divided function. -/
theorem horizontalParameterEquiv_base {S : Type*} [CommRing S]
    (V : WeierstrassCurve S) (s t b3 b4 b6 c3 c4 c6 : S)
    (hs : s = t) (h3 : b3 = c3) (h4 : b4 = c4) (h6 : b6 = c6)
    (z : WeierstrassDilatation.Coordinate V s b3 b4 b6) :
    WeierstrassDilatation.horizontalParameterEquiv V s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6
      (algebraMap _ _ z) = algebraMap _ _
        (WeierstrassDilatation.parameterEquiv V s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6 z) := by
  subst t c3 c4 c6
  rfl

/-- The whole preceding boundary map extends the actual parameter-corrected contraction. -/
theorem previousBoundaryEquiv_base (z : A) :
    previousBoundaryEquiv hπ d e (algebraMap A (Localization.Away x) z) =
      algebraMap B (Localization.Away u) (fromDivided W (π ^ k) π e.b3 e.b4 e.b6 (p z)) := by
  rw [previousBoundaryEquiv, AlgEquiv.trans_apply, horizontalParameterEquiv_base]
  exact horizontalForward_base W (π ^ k) π e.b3 e.b4 e.b6 _

/-- The spectrum of this algebra equivalence is exactly the original boundary identification. -/
theorem previousBoundaryEquiv_spec :
    Spec.map (CommRingCat.ofHom (previousBoundaryEquiv hπ d e).toRingHom) =
      (horizontalIso W (π ^ k) π e.b3 e.b4 e.b6).hom ≫
        (previousBoundaryIso hπ d e).hom := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The actual preceding attachment factors through the full horizontal localization. -/
@[reassoc] theorem previousBoundaryEquiv_previousToX :
    Spec.map (CommRingCat.ofHom (previousBoundaryEquiv hπ d e).toRingHom) ≫
      previousToX hπ d e = horizontalOpenInclusion W (π ^ k) π e.b3 e.b4 e.b6 := by
  rw [previousBoundaryEquiv_spec, previousToX]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
