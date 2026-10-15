/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNodeRestrictionSquare
public import FLT.Mazur.SuccessiveIncidencePolygonRestriction

/-!
# The original polygon node chart commutes with coefficient restriction

The square uses the existing tensor coefficient projection on the polygon
node and the original three-coordinate restriction on the Weierstrass chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap (algebraMap R S)) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "f" => algebraMap R S

/-- The constructed original polygon open preserves the actual coefficient projection. -/
@[reassoc] theorem nilpotentPolygonChart_restriction_square :
    PolygonSmoothing.chartCoefficient R S π ≫
      nilpotentPolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 =
    nilpotentPolygonChart (W.map f) (f s) (f π) (f b3) (f b4) (f b6) J hJ
      (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) ≫
        Spec.map (CommRingCat.ofHom (coefficientRingMap f W s π b3 b4 b6)) := by
  simp only [nilpotentPolygonChart, ← Category.assoc]
  rw [SuccessiveIncidence.toPolygon_restriction_square]
  simp only [Category.assoc]
  rw [nilpotentNodeChart_restriction_square]

end FLT.Mazur.WeierstrassSuccessiveX
