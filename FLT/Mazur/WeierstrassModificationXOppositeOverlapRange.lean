/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlap
public import FLT.Mazur.WeierstrassModificationXArithmeticNodeOverlap

/-!
# The full opposite initial overlap has the same standard puncture image

Reflection exchanges the actual two denominators. Thus the second leg of
the original intersection also fills D(q), with every correction retained.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "L" => PolynomialNodeOpen W s
local notation "E" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "D" => polynomialOppositeDenominator W s b3 b4 b6 r
local notation "f" => polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "g" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "P" => polynomialNodeOverlapInclusion W s
local notation "B" => polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3

/-- The first node pulls back along the opposite chart to the same full D(q). -/
theorem polynomialOppositeNodeChart_first_preimage :
    g ⁻¹' Set.range f = Set.range P := by
  rw [polynomialNodeChart_range, polynomialOppositeNodeChart_eq_spec,
    polynomialNodeOverlapInclusion_range]
  ext z
  change E (initialReflection W s b3 b4 b6
    (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁)) ∉ z.asIdeal ↔ _
  rw [initialReflection_denominator]
  exact not_congr
    (polynomialNodeForwardBase_oppositeDenominator_mem_iff W s b3 b4 b6 r hr I hI hrI h3 z)

/-- Both original overlap legs have exactly the standard puncture as their image. -/
theorem polynomialNodeOverlapOpposite_range : Set.range B = Set.range P := by
  rw [← polynomialOppositeNodeChart_first_preimage W s b3 b4 b6 r hr I hI hrI h3]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨P z, (congrArg (fun h ↦ h z)
      (polynomialNodeOverlapOpposite_global W s b3 b4 b6 r hr I hI hrI h3)).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
      (polynomialNodeOverlap_isPullback W s b3 b4 b6 r hr I hI hrI h3) y x hy
    exact ⟨z, hz⟩

end FLT.Mazur.WeierstrassModificationX
