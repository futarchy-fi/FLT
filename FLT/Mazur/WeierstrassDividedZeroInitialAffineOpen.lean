/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialAffinePolygon
public import FLT.Mazur.WeierstrassDividedZeroMobiusInitialIntersection

/-!
# The whole original initial zero-fiber affine chart embeds in the polygon

No extra identifications occur between the two fractional node charts.
The glued comparison is injective and is an open immersion on its original
open cover, hence is an open immersion on the entire initial affine scheme.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (k : ℕ)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)
local instance zeroInitialAffineOpen_nilpotent : Fact (IsNilpotent (0 : R)) := ⟨1, by simp⟩
local notation "C" => polynomialNodeOpenCover W 0 b3 b4 b6 r hr I hI hrI h3 ha
local notation "F" => polynomialNodeChart W 0 b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialOppositeNodeChart W 0 b3 b4 b6 r hr I hI hrI h3
local notation "f" => zeroInitialAffinePolygonMap W ha k b3 b4 b6 r hr I hI hrI h3 hbot

/-- The entire original initial affine comparison makes no extra point identifications. -/
theorem zeroInitialAffinePolygonMap_injective : Function.Injective f := by
  intro x y h
  obtain ⟨a, x, rfl⟩ := (C).exists_eq x
  obtain ⟨b, y, rfl⟩ := (C).exists_eq y
  change Bool at a b
  have hx := congrArg (fun g ↦ g x)
    (zeroInitialAffinePolygonMap_chart W ha k b3 b4 b6 r hr I hI hrI h3 hbot a)
  have hy := congrArg (fun g ↦ g y)
    (zeroInitialAffinePolygonMap_chart W ha k b3 b4 b6 r hr I hI hrI h3 hbot b)
  have he : zeroInitialMobiusPolygonMap W ha k a x = zeroInitialMobiusPolygonMap W ha k b y :=
    hx.symm.trans (h.trans hy)
  cases a <;> cases b
  · exact congrArg F ((zeroInitialMobiusPolygonMap W ha k false).isOpenEmbedding.injective he)
  · exact zeroInitialMobiusPolygonMap_cross_eq W ha k b3 b4 b6 r hr I hI hrI h3 hbot x y he
  · exact (zeroInitialMobiusPolygonMap_cross_eq W ha k b3 b4 b6 r hr I hI hrI h3 hbot
      y x he.symm).symm
  · exact congrArg G ((zeroInitialMobiusPolygonMap W ha k true).isOpenEmbedding.injective he)

/-- The whole original initial affine scheme, not only its two nodes, embeds in the polygon. -/
instance zeroInitialAffinePolygonMap_isOpenImmersion : IsOpenImmersion f := by
  apply IsOpenImmersion.of_openCover_source f C
    (zeroInitialAffinePolygonMap_injective W ha k b3 b4 b6 r hr I hI hrI h3 hbot)
  intro b
  change Bool at b
  change IsOpenImmersion ((if b then G else F) ≫ f)
  rw [zeroInitialAffinePolygonMap_chart]
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
