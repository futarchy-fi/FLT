/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The product of two integral affine Weierstrass charts

The tensor product of the actual normalized cubic coordinate algebras carries
two universal affine solutions. Algebra maps out of it preserve both equations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- A map from the Z = 1 chart yields an affine solution over its target algebra. -/
theorem affine_equation_of_hom (f : Coordinate W 2 →ₐ[R] S) :
    (W.map (algebraMap R S)).toAffine.Equation (f (coord W 2 0)) (f (coord W 2 1)) := by
  have h := (coord_equation W 2).map f.toRingHom
  change ((W.map (algebraMap R (Coordinate W 2))).map f.toRingHom).toProjective.Equation
    (f ∘ coord W 2) at h
  have hf : (W.map (algebraMap R (Coordinate W 2))).map f.toRingHom =
      W.map (algebraMap R S) := by
    ext <;> exact f.commutes _
  rw [hf] at h
  apply (Projective.equation_some ..).mp
  convert h using 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · change 1 = f (coord W 2 2)
    rw [coord_self, map_one]

/-- Coordinate algebra of the product of the two Z = 1 charts. -/
def AffineProduct := Coordinate W 2 ⊗[R] Coordinate W 2

instance : CommRing (AffineProduct W) :=
  inferInstanceAs (CommRing (Coordinate W 2 ⊗[R] Coordinate W 2))

instance : Algebra R (AffineProduct W) :=
  inferInstanceAs (Algebra R (Coordinate W 2 ⊗[R] Coordinate W 2))

/-- First universal point of the product. -/
def productLeft : Coordinate W 2 →ₐ[R] AffineProduct W :=
  Algebra.TensorProduct.includeLeft

/-- Second universal point of the product. -/
def productRight : Coordinate W 2 →ₐ[R] AffineProduct W :=
  Algebra.TensorProduct.includeRight

/-- First x-coordinate. -/
def productX₁ : AffineProduct W := productLeft W (coord W 2 0)

/-- First y-coordinate. -/
def productY₁ : AffineProduct W := productLeft W (coord W 2 1)

/-- Second x-coordinate. -/
def productX₂ : AffineProduct W := productRight W (coord W 2 0)

/-- Second y-coordinate. -/
def productY₂ : AffineProduct W := productRight W (coord W 2 1)

/-- The first universal point remains on the cubic after any algebra map. -/
theorem productLeft_equation (f : AffineProduct W →ₐ[R] S) :
    (W.map (algebraMap R S)).toAffine.Equation (f (productX₁ W)) (f (productY₁ W)) :=
  affine_equation_of_hom W (f.comp (productLeft W))

/-- The second universal point remains on the cubic after any algebra map. -/
theorem productRight_equation (f : AffineProduct W →ₐ[R] S) :
    (W.map (algebraMap R S)).toAffine.Equation (f (productX₂ W)) (f (productY₂ W)) :=
  affine_equation_of_hom W (f.comp (productRight W))

end FLT.Mazur.WeierstrassIntegralChart
