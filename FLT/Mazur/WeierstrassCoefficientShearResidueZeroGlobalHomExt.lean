/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroPositiveRetainedDetection
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroFirstRetainedDetection
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorInfinity

/-!
# Full original start-zero components determine global morphisms

Every full atlas chart is detected by the independently constructed component family.
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
local notation "ρ" => ProjectiveLine.endpointReversal Q

variable {Y : Scheme} (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)

/-- The original full exterior, adjacent pairs and equality component detect global maps. -/
theorem coefficientShearResidueZeroFullComponents_hom_ext
    (hF : F ≫ u = F ≫ v) (hB : ∀ j k, B j k ≫ u = B j k ≫ v)
    (hT : T ≫ u = T ≫ v) : u = v := by
  apply (coefficientShearGluingCover hπ data Q r (s + 1) hs).gluedCover.openCover.hom_ext
  intro i
  change coefficientShearGluedChart hπ data Q r (s + 1) hs i.down ≫ u =
    coefficientShearGluedChart hπ data Q r (s + 1) hs i.down ≫ v
  rcases i.down with i | j
  · fin_cases i
    · exact coefficientShearResidueInfinityChart_hom_ext
        hπ data (s + 1) hs d (by dsimp; omega) hres a
          (residueTangentComponentUnit_val W h3 h4 hc) u v hF
    · exact coefficientShearResidueZeroEqualityDivided_hom_ext
        hπ hm data s hs he h3 h4 h6next hc u v hT
    · exact coefficientShearResidueZeroInitialChart_hom_ext
        hπ hm data s hs hk h3 h4 hc u v hF
  · by_cases hj0 : j.val = 0
    · have hj : j = ⟨0, Nat.zero_lt_succ s⟩ := Fin.ext hj0
      subst j
      exact coefficientShearResidueZeroFirstRetained_hom_ext
        hπ hm data s hs he h3 h4 h6next hc u v hF hB hT
    · exact coefficientShearResidueZeroPositiveRetained_hom_ext
        hπ hm data s hs he h3 h4 h6next hc u v j (Nat.pos_of_ne_zero hj0) hB hT

end FLT.Mazur.WeierstrassDividedDepth
