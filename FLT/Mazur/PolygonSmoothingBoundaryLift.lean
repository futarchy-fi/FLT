/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingCompatibleLaurentLift

/-!
# Constructing full node maps from compatible Laurent boundaries

Two coefficient equations for each generator suffice. The actual node
relation follows from the two given algebra maps and joint detection by
both branches. Thus the construction does not assume a whole-chart map.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R] (s t : R)
  (f g : ChartRing s →ₐ[R] R[T;T⁻¹])
  (hx : LaurentCompatible t (f (leftCoordinate s)) (g (leftCoordinate s)))
  (hy : LaurentCompatible t (f (rightCoordinate s)) (g (rightCoordinate s)))
local notation "X" => pairedLaurentLift t (f (leftCoordinate s)) (g (leftCoordinate s))
local notation "Y" => pairedLaurentLift t (f (rightCoordinate s)) (g (rightCoordinate s))

include hx hy

/-- The explicitly reconstructed coordinates satisfy the complete original node relation. -/
theorem boundaryLift_relation : X * Y = algebraMap R (ChartRing t) s := by
  apply pairedLaurent_ext t
  · rw [map_mul, pairedLaurentLift_left t _ _ hx, pairedLaurentLift_left t _ _ hy,
      ← map_mul, coordinate_relation, AlgHom.commutes, AlgHom.commutes]
  · rw [map_mul, pairedLaurentLift_preceding t _ _ hx,
      pairedLaurentLift_preceding t _ _ hy, ← map_mul, coordinate_relation,
      AlgHom.commutes, AlgHom.commutes]

/-- The full node map is built from complementary Laurent lifts of its two coordinates. -/
def boundaryLift : ChartRing s →ₐ[R] ChartRing t :=
  evaluate s X Y (boundaryLift_relation s t f g hx hy)

/-- The first coordinate retains its full constructed Laurent expression. -/
@[simp] theorem boundaryLift_left :
    boundaryLift s t f g hx hy (leftCoordinate s) = X := evaluate_left ..

/-- The second coordinate retains its full constructed Laurent expression. -/
@[simp] theorem boundaryLift_right :
    boundaryLift s t f g hx hy (rightCoordinate s) = Y := evaluate_right ..

/-- The full outgoing restriction of the constructed map is the original prescribed map. -/
theorem leftLaurentMap_boundaryLift :
    (leftLaurentMap t).comp (boundaryLift s t f g hx hy) = f := by
  apply chartRing_hom_ext s
  · simpa only [AlgHom.comp_apply, boundaryLift_left] using
      pairedLaurentLift_left t _ _ hx
  · simpa only [AlgHom.comp_apply, boundaryLift_right] using
      pairedLaurentLift_left t _ _ hy

/-- The full incoming restriction of the same map is the other prescribed map. -/
theorem precedingLaurentMap_boundaryLift :
    (precedingLaurentMap R t).comp (boundaryLift s t f g hx hy) = g := by
  apply chartRing_hom_ext s
  · simpa only [AlgHom.comp_apply, boundaryLift_left] using
      pairedLaurentLift_preceding t _ _ hx
  · simpa only [AlgHom.comp_apply, boundaryLift_right] using
      pairedLaurentLift_preceding t _ _ hy

/-- A full chart map with these two original restrictions is necessarily the constructed one. -/
theorem boundaryLift_unique (F : ChartRing s →ₐ[R] ChartRing t)
    (hl : (leftLaurentMap t).comp F = f)
    (hr : (precedingLaurentMap R t).comp F = g) : F = boundaryLift s t f g hx hy := by
  apply AlgHom.ext
  intro z
  apply pairedLaurent_ext t
  · exact (DFunLike.congr_fun hl z).trans
      (DFunLike.congr_fun (leftLaurentMap_boundaryLift s t f g hx hy) z).symm
  · exact (DFunLike.congr_fun hr z).trans
      (DFunLike.congr_fun (precedingLaurentMap_boundaryLift s t f g hx hy) z).symm

omit hx hy in
/-- Full-node extension is equivalent to explicit coefficient equations on just two generators. -/
theorem boundaryLift_exists_iff :
    (∃ F : ChartRing s →ₐ[R] ChartRing t,
      (leftLaurentMap t).comp F = f ∧ (precedingLaurentMap R t).comp F = g) ↔
    LaurentCompatible t (f (leftCoordinate s)) (g (leftCoordinate s)) ∧
      LaurentCompatible t (f (rightCoordinate s)) (g (rightCoordinate s)) := by
  constructor
  · rintro ⟨F, rfl, rfl⟩
    exact ⟨laurentCompatible_restrictions t (F (leftCoordinate s)),
      laurentCompatible_restrictions t (F (rightCoordinate s))⟩
  · rintro ⟨hx, hy⟩
    exact ⟨boundaryLift s t f g hx hy, leftLaurentMap_boundaryLift s t f g hx hy,
      precedingLaurentMap_boundaryLift s t f g hx hy⟩

end FLT.Mazur.PolygonSmoothing
