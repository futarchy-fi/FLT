/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps

/-!
# Gluing every full original residue atlas map of the pinching cocone

Full pullback compatibility constructs a morphism on the actual coefficient
model and its equation gluing. Every entire original chart is retained.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)
    (Nat.zero_lt_succ (2 * s + 2)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

/-- Glue an actual original pinching cocone over the entire coefficient pullback. -/
@[irreducible] def coefficientShearResidueStrictZeroTensorCoconeDesc :
    finiteGlobalTensorModel hπ data Q (s + 1) hs ⟶ C.pt.left :=
  (cover).glueMorphisms (fun i => D i.down) (fun i j =>
    coefficientShearResidueStrictZeroAtlasCoconeMap_compatible
      hπ hm data s hs hk h3 h4 h6 hc C i.down j.down)

/-- Every whole original tensor atlas equation is recovered by the glued map. -/
theorem coefficientShearResidueStrictZeroTensorCoconeDesc_chart (i : Fin 3 ⊕ Fin (s + 1)) :
    A i ≫ coefficientShearResidueStrictZeroTensorCoconeDesc
      hπ hm data s hs hk h3 h4 h6 hc C = D i := by
  rw [coefficientShearResidueStrictZeroTensorCoconeDesc]
  exact (cover).ι_glueMorphisms _ _ ⟨i⟩

/-- The original pinching cocone descends onto the entire actual equation gluing. -/
@[irreducible] def coefficientShearResidueStrictZeroGluedCoconeDesc :
    coefficientShearGlued hπ data Q r (s + 1) hs ⟶ C.pt.left :=
  (G).hom ≫ coefficientShearResidueStrictZeroTensorCoconeDesc
    hπ hm data s hs hk h3 h4 h6 hc C

/-- Every full chart of the actual equation gluing keeps the original cocone map. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_chart
    (i : Fin 3 ⊕ Fin (s + 1)) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs i ≫
      coefficientShearResidueStrictZeroGluedCoconeDesc
        hπ hm data s hs hk h3 h4 h6 hc C = D i := by
  rw [coefficientShearResidueStrictZeroGluedCoconeDesc, coefficientShearGluedIso_chart_assoc,
    coefficientShearResidueStrictZeroTensorCoconeDesc_chart]

/-- The full original atlas restrictions uniquely determine the tensor cocone descent. -/
theorem coefficientShearResidueStrictZeroTensorCoconeDesc_unique
    (f : finiteGlobalTensorModel hπ data Q (s + 1) hs ⟶ C.pt.left)
    (hf : ∀ i, A i ≫ f = D i) :
    f = coefficientShearResidueStrictZeroTensorCoconeDesc
      hπ hm data s hs hk h3 h4 h6 hc C := by
  apply (cover).hom_ext
  intro i
  exact (hf i.down).trans
    (coefficientShearResidueStrictZeroTensorCoconeDesc_chart
      hπ hm data s hs hk h3 h4 h6 hc C i.down).symm

/-- The full original equation restrictions uniquely determine the glued cocone descent. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_unique
    (f : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ C.pt.left)
    (hf : ∀ i, coefficientShearGluedChart hπ data Q r (s + 1) hs i ≫ f = D i) :
    f = coefficientShearResidueStrictZeroGluedCoconeDesc
      hπ hm data s hs hk h3 h4 h6 hc C := by
  have h : (G).inv ≫ f = coefficientShearResidueStrictZeroTensorCoconeDesc
      hπ hm data s hs hk h3 h4 h6 hc C := by
    apply coefficientShearResidueStrictZeroTensorCoconeDesc_unique
    intro i
    rw [← coefficientShearGluedIso_chart hπ data Q r (s + 1) hs i,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact hf i
  rw [coefficientShearResidueStrictZeroGluedCoconeDesc, ← h, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
