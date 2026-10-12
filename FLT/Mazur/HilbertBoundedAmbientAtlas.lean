/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedPolynomialAtlas
public import FLT.Mazur.HilbertAmbientClosedParameter
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Finite affine atlases retaining all ambient equations

Restrict the bounded polynomial atlas along the actual closed ambient Hilbert
immersion. Its charts remain affine and retain every ambient equation. For
finitely many ambient generators this proves quasi-compactness of the actual
ambient Hilbert scheme, without assuming finite generation of its relation ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false

universe u
variable (R I : Type u) [CommRing R] (d : ℕ) (K : Ideal (MvPolynomial I R))

/-- Pull back the finite polynomial atlas along the full ambient closed immersion. -/
def boundedAmbientHilbertCover : (ambientHilbertScheme R I d K).OpenCover :=
  (boundedPolynomialHilbertCover R I d).pullback₁ (ambientHilbertι R I d K)

instance [Finite I] : Finite (boundedAmbientHilbertCover R I d K).I₀ :=
  inferInstanceAs (Finite (Fin d → BoundedHilbertMonomials I d))

/-- The actual restriction to each bounded chart is a closed subscheme of an affine spectrum. -/
instance boundedAmbientHilbertCover_isAffine (m : (boundedAmbientHilbertCover R I d K).I₀) :
    IsAffine ((boundedAmbientHilbertCover R I d K).X m) := by
  change IsAffine (pullback (ambientHilbertι R I d K)
    ((boundedPolynomialHilbertCover R I d).f m))
  infer_instance

/-- All ambient equations survive the cartesian restriction to a bounded polynomial chart. -/
theorem boundedAmbientHilbertChart_isPullback
    (m : Fin d → BoundedHilbertMonomials I d) :
    IsPullback
      (pullback.fst (ambientHilbertι R I d K) ((boundedPolynomialHilbertCover R I d).f m))
      (pullback.snd (ambientHilbertι R I d K) ((boundedPolynomialHilbertCover R I d).f m))
      (ambientHilbertι R I d K) ((boundedPolynomialHilbertCover R I d).f m) :=
  IsPullback.of_hasPullback _ _

/-- The actual closed ambient Hilbert parameter scheme is quasi-compact for finite variables. -/
instance ambientHilbertScheme_compactSpace [Finite I] :
    CompactSpace (ambientHilbertScheme R I d K) :=
  (boundedAmbientHilbertCover R I d K).compactSpace

end FLT.Mazur.HilbertChart
