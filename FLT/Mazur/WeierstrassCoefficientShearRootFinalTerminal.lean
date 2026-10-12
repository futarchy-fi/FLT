/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalOriginal
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalZeroOriginal
public import FLT.Mazur.WeierstrassCoefficientShearOriginalFinalTerminal

/-!
# Independent terminal projective pairs at the original final indices

Select the independently constructed terminal pair by the actual preceding
scale, and recover the original final components and both indexed node maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "V" => W.map (residue R)
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (divided_linear_mem D (start + (j + 1)) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (divided_linear_mem D (start + (j + 1)) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h6" => Iff.mpr (residue_eq_zero_iff _)
  (divided_constant_mem D (start + (j + 1)) hp (Data.b6 d) (Data.factor6 d))
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => residueTangentUnit D
local notation "ha" => Eq.trans (residueTangentUnit_val D) (Eq.symm (rootShearZero_tangent V))
local notation "hπ₀" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "G" => coefficientShearGluedIso hπ data K 0 (j + 1) hj
local notation "p" => coefficientShearGluedStructure hπ data K 0 (j + 1) hj

/-- The independently glued full terminal pair with the original two ordered final indices. -/
def coefficientShearRootFinalTerminalComponent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (j + 1) hj :=
  if h : 0 < start + j then
    let hs := WeierstrassDilatation.residue_scale_eq_zero D (start + j) h
    Fin.cases
      (coefficientShearRootTerminalFirstComponent
        hπ data K 0 j hj hs hπ₀ h3 h4 h6 hr a ha)
      (fun _ => coefficientShearRootTerminalSecondComponent
        hπ data K 0 j hj hs hπ₀ h3 h4 h6 hr a ha) i
  else
    let hs : algebraMap R K (π ^ (start + j)) = 1 := by
      rw [show start + j = 0 by omega, pow_zero, map_one]
    Fin.cases
      (coefficientShearRootTerminalZeroFirstComponent
        hπ data K 0 j hj hs hπ₀ h3 h4 h6 hr a ha)
      (fun _ => coefficientShearRootTerminalZeroSecondComponent
        hπ data K 0 j hj hs hπ₀ h3 h4 h6 hr a ha) i

/-- The independent pair recovers the complete earlier pair without changing either final index. -/
theorem coefficientShearRootFinalTerminalComponent_eq (i : Fin 2) :
    coefficientShearRootFinalTerminalComponent hπ data D j hj hk hp i =
      coefficientShearFinalTerminalComponent hπ data D j hj hk hp i := by
  unfold coefficientShearRootFinalTerminalComponent
  split_ifs with h
  · rw [coefficientShearFinalTerminalComponent_positive hπ data D j hj hk hp h]
    fin_cases i
    · exact coefficientShearRootTerminalFirstComponent_rootZero hπ data D j hj h hk hp
    · exact coefficientShearRootTerminalSecondComponent_rootZero hπ data D j hj h hk hp
  · rw [coefficientShearFinalTerminalComponent_zero_depth hπ data D j hj hk hp (by omega)]
    fin_cases i
    · exact coefficientShearRootTerminalZeroFirstComponent_rootZero
        hπ data D j hj (by omega) hk hp
    · exact coefficientShearRootTerminalZeroSecondComponent_rootZero
        hπ data D j hj (by omega) hk hp

/-- Both complete independent terminal components reconstruct at their actual original indices. -/
@[reassoc] theorem coefficientShearRootFinalTerminalComponent_original (i : Fin 2) :
    coefficientShearRootFinalTerminalComponent hπ data D j hj hk hp i ≫ (G).hom =
      finalTerminalComponent hπ data D j hj hk hp i := by
  rw [coefficientShearRootFinalTerminalComponent_eq,
    coefficientShearFinalTerminalComponent_original]

/-- The entire independent pair is defined over the original residue field. -/
@[reassoc] theorem coefficientShearRootFinalTerminalComponent_structure (i : Fin 2) :
    coefficientShearRootFinalTerminalComponent hπ data D j hj hk hp i ≫ p =
      ProjectiveLine.toBase K := by
  rw [coefficientShearRootFinalTerminalComponent_eq,
    coefficientShearFinalTerminalComponent_structure]

/-- The zero marking keeps the actual last retained-node index and branch order. -/
@[reassoc] theorem coefficientShearRootFinalTerminalComponent_zero_original (i : Fin 2) :
    ProjectiveLine.zero K ≫
        coefficientShearRootFinalTerminalComponent hπ data D j hj hk hp i ≫ (G).hom =
      finalNodeSection hπ data D j hj hk hp (.inl (.inr (⟨j, by omega⟩, i))) := by
  rw [coefficientShearRootFinalTerminalComponent_original, finalTerminalComponent_zero]

/-- Both infinity markings keep the single original final terminal-node index. -/
@[reassoc] theorem coefficientShearRootFinalTerminalComponent_infinity_original (i : Fin 2) :
    ProjectiveLine.infinity K ≫
        coefficientShearRootFinalTerminalComponent hπ data D j hj hk hp i ≫ (G).hom =
      finalNodeSection hπ data D j hj hk hp (.inr ()) := by
  rw [coefficientShearRootFinalTerminalComponent_original, finalTerminalComponent_infinity]

/-- The independent indexed terminal component as a morphism over the original residue field. -/
def coefficientShearRootFinalTerminalOverComponent (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (coefficientShearRootFinalTerminalComponent hπ data D j hj hk hp i)
    (coefficientShearRootFinalTerminalComponent_structure hπ data D j hj hk hp i)

end FLT.Mazur.WeierstrassDividedDepth
