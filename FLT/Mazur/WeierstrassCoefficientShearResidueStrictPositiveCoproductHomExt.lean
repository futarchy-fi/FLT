/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveGlobalHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleReflection

/-!
# The full original strict positive-start normalization detects global morphisms

The original odd cyclic component coproduct is an epimorphism, with no
affine hypothesis on the target. This supplies uniqueness for pinching descent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
attribute [local irreducible] coefficientShearGlued
  coefficientShearResidueStrictPositiveCycleComponent
  coefficientShearResidueStrictPositiveCycleCoproduct
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueStrictPositiveBranch
  hπ hm data s hs hk h3 h4 h6 hc hstart
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueStrictPositiveCycleComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "N" => coefficientShearResidueStrictPositiveCycleCoproduct
  hπ hm data s hs hk hstart h3 h4 h6 hc
variable {Y : Scheme}
  (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)

/-- The full cyclic component family detects maps on every actual atlas chart. -/
theorem coefficientShearResidueStrictPositiveCycle_hom_ext
    (hC : ∀ i, C i ≫ u = C i ≫ v) : u = v := by
  have hB : ∀ j k, B j k ≫ u = B j k ≫ v := by
    intro j k
    fin_cases k
    · change B j 0 ≫ u = B j 0 ≫ v
      have h := hC ⟨j.val + 1, by omega⟩
      rw [coefficientShearResidueStrictPositiveCycleComponent_first] at h
      apply (cancel_epi (ProjectiveLine.endpointReversalIso Q).hom).mp
      simpa only [Category.assoc, ProjectiveLine.endpointReversalIso] using h
    · change B j 1 ≫ u = B j 1 ≫ v
      simpa only [coefficientShearResidueStrictPositiveCycleComponent_second] using
        hC ⟨2 * s + 4 - j.val, by omega⟩
  apply coefficientShearResidueStrictPositiveFullComponents_hom_ext
    hπ hm data s hs hk hstart h3 h4 h6 hc u v
  · simpa only [coefficientShearResidueStrictPositiveCycleComponent_exterior] using hC 0
  · intro j k
    simpa only [coefficientShearResidueStrictPositiveBranch_branch] using hB j.castSucc k
  · intro k
    simpa only [coefficientShearResidueStrictPositiveBranch_terminal] using hB (Fin.last (s + 1)) k

/-- The entire original normalization coproduct detects arbitrary scheme morphisms. -/
theorem coefficientShearResidueStrictPositiveCycleCoproduct_hom_ext
    (hN : (N).left ≫ u = (N).left ≫ v) : u = v := by
  apply coefficientShearResidueStrictPositiveCycle_hom_ext
    hπ hm data s hs hk hstart h3 h4 h6 hc u v
  intro i
  have h := congrArg (fun f => (PolygonPinching.componentι Q (2 * s + 5) i).left ≫ f) hN
  simpa only [coefficientShearResidueStrictPositiveCycleCoproduct_ι_assoc] using h

/-- The full original strict positive-start normalization is categorically epic. -/
theorem coefficientShearResidueStrictPositiveCycleCoproduct_epi : Epi (N).left := by
  constructor
  intro Y u v hN
  exact coefficientShearResidueStrictPositiveCycleCoproduct_hom_ext
    hπ hm data s hs hk hstart h3 h4 h6 hc u v hN

/-- The same original normalization detects arbitrary morphisms over the residue field. -/
theorem coefficientShearResidueStrictPositiveCycleOver_hom_ext
    {Y : Over (Spec (.of Q))}
    (f g : Over.mk (coefficientShearGluedStructure hπ data Q r (s + 1) hs) ⟶ Y)
    (h : N ≫ f = N ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  exact coefficientShearResidueStrictPositiveCycleCoproduct_hom_ext
    hπ hm data s hs hk hstart h3 h4 h6 hc f.left g.left
    (congrArg (fun t => t.left) h)

end FLT.Mazur.WeierstrassDividedDepth
