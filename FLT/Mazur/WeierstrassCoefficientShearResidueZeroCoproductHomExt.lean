/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroGlobalHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityReflection

/-!
# The actual complete cyclic coproduct detects global morphisms

Agreement on the original coproduct implies agreement on the exterior, both
complete branches, and the terminal component, including the reversed parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "C" => coefficientShearResidueZeroEqualityCycleComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "N" => coefficientShearResidueZeroEqualityCycleCoproduct
  hπ hm data s hs he h3 h4 h6next hc
variable {Y : Scheme}
  (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)

/-- The original cyclic ordering detects equality on every full component. -/
theorem coefficientShearResidueZeroEqualityCycle_hom_ext
    (hC : ∀ i, C i ≫ u = C i ≫ v) : u = v := by
  apply coefficientShearResidueZeroFullComponents_hom_ext
    hπ hm data s hs he h3 h4 h6next hc u v
  · simpa only [coefficientShearResidueZeroEqualityCycleComponent_exterior] using hC 0
  · intro j i
    fin_cases i
    · change B j 0 ≫ u = B j 0 ≫ v
      have h := hC ⟨j.val + 1, by omega⟩
      rw [coefficientShearResidueZeroEqualityCycleComponent_first] at h
      apply (cancel_epi (ProjectiveLine.endpointReversalIso Q).hom).mp
      simpa only [Category.assoc, ProjectiveLine.endpointReversalIso] using h
    · change B j 1 ≫ u = B j 1 ≫ v
      simpa only [coefficientShearResidueZeroEqualityCycleComponent_second] using
        hC ⟨2 * s + 1 - j.val, by omega⟩
  · have h := hC ⟨s + 1, by omega⟩
    rw [coefficientShearResidueZeroEqualityCycleComponent_terminal] at h
    apply (cancel_epi (ProjectiveLine.endpointReversalIso Q).hom).mp
    simpa only [Category.assoc, ProjectiveLine.endpointReversalIso] using h

/-- The actual cyclic normalization coproduct is an epimorphism of schemes. -/
theorem coefficientShearResidueZeroEqualityCycleCoproduct_hom_ext
    (hN : (N).left ≫ u = (N).left ≫ v) : u = v := by
  apply coefficientShearResidueZeroEqualityCycle_hom_ext
    hπ hm data s hs he h3 h4 h6next hc u v
  intro i
  have h := congrArg (fun f => (PolygonPinching.componentι Q (2 * s + 2) i).left ≫ f) hN
  simpa only [coefficientShearResidueZeroEqualityCycleCoproduct_ι_assoc] using h

/-- The underlying map of the complete actual component coproduct is categorically epic. -/
theorem coefficientShearResidueZeroEqualityCycleCoproduct_epi : Epi (N).left := by
  constructor
  intro Y u v hN
  exact coefficientShearResidueZeroEqualityCycleCoproduct_hom_ext
    hπ hm data s hs he h3 h4 h6next hc u v hN

end FLT.Mazur.WeierstrassDividedDepth
