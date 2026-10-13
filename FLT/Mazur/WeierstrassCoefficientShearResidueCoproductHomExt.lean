/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueGlobalHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueCycleReflection

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
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "C" => coefficientShearResidueCycleComponent
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "N" => coefficientShearResidueCycleCoproduct
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
variable {Y : Scheme}
  (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)

/-- The original cyclic ordering detects equality on every full component. -/
theorem coefficientShearResidueCycle_hom_ext
    (hC : ∀ i, C i ≫ u = C i ≫ v) : u = v := by
  apply coefficientShearResidueFullComponents_hom_ext
    hπ hm data s hs he hstart h3 h4 h6 h6next hc u v
  · simpa only [coefficientShearResidueCycleComponent_exterior] using hC 0
  · intro j i
    fin_cases i
    · change B j 0 ≫ u = B j 0 ≫ v
      have h := hC ⟨j.val + 1, by omega⟩
      rw [coefficientShearResidueCycleComponent_first] at h
      apply (cancel_epi (ProjectiveLine.endpointReversalIso Q).hom).mp
      simpa only [Category.assoc, ProjectiveLine.endpointReversalIso] using h
    · change B j 1 ≫ u = B j 1 ≫ v
      simpa only [coefficientShearResidueCycleComponent_second] using
        hC ⟨2 * s + 3 - j.val, by omega⟩
  · have h := hC ⟨s + 2, by omega⟩
    rw [coefficientShearResidueCycleComponent_terminal] at h
    apply (cancel_epi (ProjectiveLine.endpointReversalIso Q).hom).mp
    simpa only [Category.assoc, ProjectiveLine.endpointReversalIso] using h

/-- The actual cyclic normalization coproduct is an epimorphism of schemes. -/
theorem coefficientShearResidueCycleCoproduct_hom_ext
    (hN : (N).left ≫ u = (N).left ≫ v) : u = v := by
  apply coefficientShearResidueCycle_hom_ext
    hπ hm data s hs he hstart h3 h4 h6 h6next hc u v
  intro i
  have h := congrArg (fun f => (PolygonPinching.componentι Q (2 * s + 4) i).left ≫ f) hN
  simpa only [coefficientShearResidueCycleCoproduct_ι_assoc] using h

/-- The underlying map of the complete actual component coproduct is categorically epic. -/
theorem coefficientShearResidueCycleCoproduct_epi : Epi (N).left := by
  constructor
  intro Y u v hN
  exact coefficientShearResidueCycleCoproduct_hom_ext
    hπ hm data s hs he hstart h3 h4 h6 h6next hc u v hN

end FLT.Mazur.WeierstrassDividedDepth
