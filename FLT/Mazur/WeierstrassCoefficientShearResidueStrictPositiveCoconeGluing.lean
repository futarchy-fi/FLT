/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps

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
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 5) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 5) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictPositiveAtlasCoconeMap
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

/-- Glue an actual original pinching cocone over the entire coefficient pullback. -/
@[irreducible] def coefficientShearResidueStrictPositiveTensorCoconeDesc :
    finiteGlobalTensorModel hπ data Q (s + 1) hs ⟶ C.pt.left :=
  (cover).glueMorphisms (fun i => D i.down) (fun i j =>
    coefficientShearResidueStrictPositiveAtlasCoconeMap_compatible
      hπ hm data s hs hk hstart h3 h4 h6 hc C i.down j.down)

/-- Every whole original tensor atlas equation is recovered by the glued map. -/
theorem coefficientShearResidueStrictPositiveTensorCoconeDesc_chart (i : Fin 3 ⊕ Fin (s + 1)) :
    A i ≫ coefficientShearResidueStrictPositiveTensorCoconeDesc
      hπ hm data s hs hk hstart h3 h4 h6 hc C = D i := by
  rw [coefficientShearResidueStrictPositiveTensorCoconeDesc]
  exact (cover).ι_glueMorphisms _ _ ⟨i⟩

/-- The original pinching cocone descends onto the entire actual equation gluing. -/
@[irreducible] def coefficientShearResidueStrictPositiveGluedCoconeDesc :
    coefficientShearGlued hπ data Q r (s + 1) hs ⟶ C.pt.left :=
  (G).hom ≫ coefficientShearResidueStrictPositiveTensorCoconeDesc
    hπ hm data s hs hk hstart h3 h4 h6 hc C

/-- Every full chart of the actual equation gluing keeps the original cocone map. -/
theorem coefficientShearResidueStrictPositiveGluedCoconeDesc_chart
    (i : Fin 3 ⊕ Fin (s + 1)) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs i ≫
      coefficientShearResidueStrictPositiveGluedCoconeDesc
        hπ hm data s hs hk hstart h3 h4 h6 hc C = D i := by
  rw [coefficientShearResidueStrictPositiveGluedCoconeDesc, coefficientShearGluedIso_chart_assoc,
    coefficientShearResidueStrictPositiveTensorCoconeDesc_chart]

/-- The full original atlas restrictions uniquely determine the tensor cocone descent. -/
theorem coefficientShearResidueStrictPositiveTensorCoconeDesc_unique
    (f : finiteGlobalTensorModel hπ data Q (s + 1) hs ⟶ C.pt.left)
    (hf : ∀ i, A i ≫ f = D i) :
    f = coefficientShearResidueStrictPositiveTensorCoconeDesc
      hπ hm data s hs hk hstart h3 h4 h6 hc C := by
  apply (cover).hom_ext
  intro i
  exact (hf i.down).trans
    (coefficientShearResidueStrictPositiveTensorCoconeDesc_chart
      hπ hm data s hs hk hstart h3 h4 h6 hc C i.down).symm

/-- The full original equation restrictions uniquely determine the glued cocone descent. -/
theorem coefficientShearResidueStrictPositiveGluedCoconeDesc_unique
    (f : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ C.pt.left)
    (hf : ∀ i, coefficientShearGluedChart hπ data Q r (s + 1) hs i ≫ f = D i) :
    f = coefficientShearResidueStrictPositiveGluedCoconeDesc
      hπ hm data s hs hk hstart h3 h4 h6 hc C := by
  have h : (G).inv ≫ f = coefficientShearResidueStrictPositiveTensorCoconeDesc
      hπ hm data s hs hk hstart h3 h4 h6 hc C := by
    apply coefficientShearResidueStrictPositiveTensorCoconeDesc_unique
    intro i
    rw [← coefficientShearGluedIso_chart hπ data Q r (s + 1) hs i,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact hf i
  rw [coefficientShearResidueStrictPositiveGluedCoconeDesc, ← h, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
