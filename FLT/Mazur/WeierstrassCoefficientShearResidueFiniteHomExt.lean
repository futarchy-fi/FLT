/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueInitialHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueInteriorHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueEqualityHomExt

/-!
# Actual residue components determine every finite atlas chart

The full exterior, branch pairs and equality component detect the initial,
all retained, and divided charts. Global uniqueness reduces to the infinity chart.
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
variable {Y : Scheme}
  (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)

/-- The actual complete components detect all atlas charts except the original infinity chart. -/
theorem coefficientShearResidueFiniteCharts_hom_ext
    (hF : F ≫ u = F ≫ v) (hB : ∀ j i, B j i ≫ u = B j i ≫ v)
    (hT : T ≫ u = T ≫ v) (i : Fin 3 ⊕ Fin (s + 1)) (hi : i ≠ .inl 0) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs i ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs i ≫ v := by
  rcases i with i | j
  · fin_cases i
    · exact (hi rfl).elim
    · exact coefficientShearResidueEqualityDividedChart_hom_ext
        hπ hm data s hs he h3 h4 h6next hc hstart u v hT
    · apply coefficientShearResidueInitialChart_hom_ext
        hπ hm data s hs hk hstart h3 h4 h6 hc u v
      · simpa only [coefficientShearResidueBranchComponent_initial] using hB 0 0
      · simpa only [coefficientShearResidueBranchComponent_initial] using hB 0 1
      · exact hF
  · by_cases hj : j.val = s
    · have H : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hj
      subst j
      exact coefficientShearResidueLastRetainedChart_hom_ext
        hπ hm data s hs he h3 h4 h6next hc hstart h6 u v (hB _) hT
    · let k : Fin s := ⟨j.val, by omega⟩
      have H : j = k.castSucc := Fin.ext rfl
      rw [H]
      exact coefficientShearResidueInteriorChart_hom_ext
        hπ hm data s hs hk h3 h4 hc k hstart h6 u v (hB _) (hB _)

/-- For the whole model, the only additional uniqueness check is the original infinity chart. -/
theorem coefficientShearResidueComponents_hom_ext
    (hF : F ≫ u = F ≫ v) (hB : ∀ j i, B j i ≫ u = B j i ≫ v)
    (hT : T ≫ u = T ≫ v)
    (hinf : coefficientShearGluedChart hπ data Q r (s + 1) hs (.inl 0) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inl 0) ≫ v) : u = v := by
  apply (coefficientShearGluingCover hπ data Q r (s + 1) hs).gluedCover.openCover.hom_ext
  intro i
  change coefficientShearGluedChart hπ data Q r (s + 1) hs i.down ≫ u =
    coefficientShearGluedChart hπ data Q r (s + 1) hs i.down ≫ v
  by_cases hi : i.down = .inl 0
  · rw [hi]
    exact hinf
  · exact coefficientShearResidueFiniteCharts_hom_ext
      hπ hm data s hs he hstart h3 h4 h6 h6next hc u v hF hB hT i.down hi

end FLT.Mazur.WeierstrassDividedDepth
