/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBranchSequence

/-!
# Short exact normalization sequences on both node charts

The cyclic node uses pairs of polynomials with equal origin values. The one-gon
uses polynomials with equal values at zero and one. In both cases these are
actual structure direct images with the specified branch-difference maps.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.NodeNormalizationExact
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonNodeEqualizer PolygonNodePresentation
variable (K : Type u) [Field K]
/-- The coordinate inclusion into the normalization ring. -/
abbrev inclusion : CommRingCat.of (A (R := K)) ⟶ CommRingCat.of (K[X] × K[X]) :=
  CommRingCat.ofHom (A (R := K)).val.toRingHom
/-- Evaluation at zero on the first branch. -/
abbrev firstValue : CommRingCat.of (K[X] × K[X]) ⟶ CommRingCat.of K :=
  CommRingCat.ofHom ((Polynomial.evalRingHom (0 : K)).comp (RingHom.fst _ _))
/-- Evaluation at zero on the second branch. -/
abbrev secondValue : CommRingCat.of (K[X] × K[X]) ⟶ CommRingCat.of K :=
  CommRingCat.ofHom ((Polynomial.evalRingHom (0 : K)).comp (RingHom.snd _ _))
/-- The common value at the pinched node. -/
abbrev nodeValue : CommRingCat.of (A (R := K)) ⟶ CommRingCat.of K :=
  CommRingCat.ofHom (aEval (R := K)).toRingHom
theorem first_agrees : inclusion K ≫ firstValue K = nodeValue K := rfl
theorem second_agrees : inclusion K ≫ secondValue K = nodeValue K := by
  ext p
  exact ((mem_A _).mp p.property).symm
/-- The actual module-sheaf normalization complex of the affine node. -/
def complex : ShortComplex (Spec (.of (A (R := K)))).Modules :=
  AffineBranchSequence.complex (inclusion K) (firstValue K) (secondValue K) (nodeValue K)
    (by rw [← Spec.map_comp, first_agrees]) (by rw [← Spec.map_comp, second_agrees])
/-- The affine node has its specified normalization short exact sequence. -/
theorem shortExact : (complex K).ShortExact := by
  apply AffineBranchSequence.shortExact
  · exact Subtype.val_injective
  · intro p hp
    exact ⟨⟨p, (mem_A p).mpr hp⟩, rfl⟩
  · intro a
    exact ⟨(Polynomial.C a, 0), by simp [firstValue, secondValue]⟩
end FLT.Mazur.NodeNormalizationExact

namespace FLT.Mazur.OneGonNormalizationExact
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonNodePresentation
variable (K : Type u) [Field K]
/-- The coordinate inclusion into the normalization ring. -/
abbrev inclusion : CommRingCat.of (B (R := K)) ⟶ CommRingCat.of K[X] :=
  CommRingCat.ofHom (B (R := K)).val.toRingHom
/-- Evaluation at zero on the affine normalization. -/
abbrev zeroValue : CommRingCat.of K[X] ⟶ CommRingCat.of K :=
  CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))
/-- Evaluation at one on the affine normalization. -/
abbrev oneValue : CommRingCat.of K[X] ⟶ CommRingCat.of K :=
  CommRingCat.ofHom (Polynomial.evalRingHom (1 : K))
/-- The common value at the pinched node. -/
abbrev nodeValue : CommRingCat.of (B (R := K)) ⟶ CommRingCat.of K :=
  CommRingCat.ofHom (bEval (R := K)).toRingHom
theorem zero_agrees : inclusion K ≫ zeroValue K = nodeValue K := rfl
theorem one_agrees : inclusion K ≫ oneValue K = nodeValue K := by
  ext p
  exact ((mem_B _).mp p.property).symm
/-- The actual module-sheaf normalization complex of the affine one-gon chart. -/
def complex : ShortComplex (Spec (.of (B (R := K)))).Modules :=
  AffineBranchSequence.complex (inclusion K) (zeroValue K) (oneValue K) (nodeValue K)
    (by rw [← Spec.map_comp, zero_agrees]) (by rw [← Spec.map_comp, one_agrees])
/-- The pinched affine one-gon chart has its normalization short exact sequence. -/
theorem shortExact : (complex K).ShortExact := by
  apply AffineBranchSequence.shortExact
  · exact Subtype.val_injective
  · intro p hp
    exact ⟨⟨p, (mem_B p).mpr hp⟩, rfl⟩
  · intro a
    refine ⟨Polynomial.C a * (1 - Polynomial.X), ?_⟩
    simp [zeroValue, oneValue]
end FLT.Mazur.OneGonNormalizationExact
