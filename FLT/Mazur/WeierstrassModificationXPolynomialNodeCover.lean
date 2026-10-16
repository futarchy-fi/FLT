/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlap
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The original two full initial nodes as an open cover

The actual initial affine scheme is covered by its two constructed full
nodes. Agreement on the standard D(q) overlap suffices to glue morphisms
on this cover, with no replacement of the source scheme.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
  (ha : IsUnit W.a₁)
local notation "A" => Coordinate W s b3 b4 b6
local notation "L" => PolynomialNodeOpen W s
local notation "F" => polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3

/-- The two genuine original initial nodes, with their original inclusions. -/
def polynomialNodeOpenCover : (Spec (.of A)).OpenCover where
  I₀ := Bool
  X _ := Spec (.of L)
  f b := if b then G else F
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro z
      rcases polynomialNodeCharts_cover W s b3 b4 b6 r hr I hI hrI h3 ha z with h | h
      · obtain ⟨x, hx⟩ := h
        exact ⟨false, x, hx⟩
      · obtain ⟨x, hx⟩ := h
        exact ⟨true, x, hx⟩
    · intro b
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

variable {Y : Scheme} (f : Bool → (Spec (.of (PolynomialNodeOpen W s)) ⟶ Y))
  (hf : polynomialNodeOverlapInclusion W s ≫ f false =
    polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3 ≫ f true)

include hf in
/-- Agreement on the actual standard overlap gives the categorical cover compatibility. -/
theorem polynomialNodeOpenCover_compatible (a b : Bool) :
    pullback.fst ((polynomialNodeOpenCover W s b3 b4 b6 r hr I hI hrI h3 ha).f a)
      ((polynomialNodeOpenCover W s b3 b4 b6 r hr I hI hrI h3 ha).f b) ≫ f a =
    pullback.snd _ _ ≫ f b := by
  have pb := polynomialNodeOverlap_isPullback W s b3 b4 b6 r hr I hI hrI h3
  cases a <;> cases b
  · exact congrArg (fun t ↦ t ≫ f false) ((cancel_mono F).mp pullback.condition)
  · change pullback.fst F G ≫ f false = pullback.snd F G ≫ f true
    apply (cancel_epi pb.isoPullback.hom).mp
    simpa only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd] using hf
  · change pullback.fst G F ≫ f true = pullback.snd G F ≫ f false
    apply (cancel_epi pb.flip.isoPullback.hom).mp
    simpa only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd] using hf.symm
  · exact congrArg (fun t ↦ t ≫ f true) ((cancel_mono G).mp pullback.condition)

end FLT.Mazur.WeierstrassModificationX
