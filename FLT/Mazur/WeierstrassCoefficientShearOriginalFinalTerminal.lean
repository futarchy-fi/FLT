/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTerminalComponents
public import FLT.Mazur.WeierstrassCoefficientShearTerminalZeroComponents
public import FLT.Mazur.WeierstrassDividedFinalTerminalOverComponents
import all FLT.Mazur.WeierstrassCoefficientShearTerminalComponents
import all FLT.Mazur.WeierstrassCoefficientShearTerminalZeroComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearOriginalTerminalConics

/-!
# Sheared terminal components retain the original final indices

The independently glued pair includes both positive scale and scale one.
Reconstruction preserves the complete original maps, structure and node markings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R

/-- The ordered full terminal components, constructed from the actual affine charts. -/
def coefficientShearFinalTerminalComponent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (s + 1) hs :=
  if h : 0 < start + s then
    Fin.cases (coefficientShearTerminalFirstComponent hπ data D s hs h hk hp)
      (fun _ => coefficientShearTerminalSecondComponent hπ data D s hs h hk hp) i
  else
    Fin.cases (coefficientShearTerminalZeroFirstComponent hπ data D s hs (by omega) hk hp)
      (fun _ => coefficientShearTerminalZeroSecondComponent hπ data D s hs (by omega) hk hp) i

/-- At positive depth the pair is precisely the original terminal gluing. -/
theorem coefficientShearFinalTerminalComponent_positive (h : 0 < start + s) (i : Fin 2) :
    coefficientShearFinalTerminalComponent hπ data D s hs hk hp i =
      Fin.cases (coefficientShearTerminalFirstComponent hπ data D s hs h hk hp)
        (fun _ => coefficientShearTerminalSecondComponent hπ data D s hs h hk hp) i := by
  simp only [coefficientShearFinalTerminalComponent, dite_eq_left h]

/-- At scale one the pair is precisely the full zero-depth gluing. -/
theorem coefficientShearFinalTerminalComponent_zero_depth (h : start + s = 0) (i : Fin 2) :
    coefficientShearFinalTerminalComponent hπ data D s hs hk hp i =
      Fin.cases (coefficientShearTerminalZeroFirstComponent hπ data D s hs h hk hp)
        (fun _ => coefficientShearTerminalZeroSecondComponent hπ data D s hs h hk hp) i := by
  simp only [coefficientShearFinalTerminalComponent, dite_eq_right (show ¬0 < start + s by omega)]

local notation "G" => coefficientShearGluedIso hπ data K 0 (s + 1) hs
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs

/-- Both original final component indices survive reconstruction of the complete sheared pair. -/
@[reassoc] theorem coefficientShearFinalTerminalComponent_original (i : Fin 2) :
    coefficientShearFinalTerminalComponent hπ data D s hs hk hp i ≫ (G).hom =
      finalTerminalComponent hπ data D s hs hk hp i := by
  by_cases h : 0 < start + s
  · rw [coefficientShearFinalTerminalComponent_positive hπ data D s hs hk hp h,
      finalTerminalComponent_positive hπ data D s hs hk hp h]
    fin_cases i
    · exact coefficientShearTerminalFirstComponent_original hπ data D s hs h hk hp
    · exact coefficientShearTerminalSecondComponent_original hπ data D s hs h hk hp
  · rw [coefficientShearFinalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega),
      finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    fin_cases i
    · exact coefficientShearTerminalZeroFirstComponent_original hπ data D s hs (by omega) hk hp
    · exact coefficientShearTerminalZeroSecondComponent_original hπ data D s hs (by omega) hk hp

/-- Each full projective component preserves the actual coefficient-field projection. -/
@[reassoc] theorem coefficientShearFinalTerminalComponent_structure (i : Fin 2) :
    coefficientShearFinalTerminalComponent hπ data D s hs hk hp i ≫ p =
      ProjectiveLine.toBase K := by
  change _ ≫ (G).hom ≫ _ = _
  rw [← Category.assoc, coefficientShearFinalTerminalComponent_original,
    finalTerminalComponent_structure]

/-- Both zero markings reconstruct the actual indexed retained nodes. -/
@[reassoc] theorem coefficientShearFinalTerminalComponent_zero_original (i : Fin 2) :
    ProjectiveLine.zero K ≫
        coefficientShearFinalTerminalComponent hπ data D s hs hk hp i ≫ (G).hom =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (⟨s, by omega⟩, i))) := by
  rw [coefficientShearFinalTerminalComponent_original, finalTerminalComponent_zero]

/-- Both infinity markings reconstruct the single actual terminal node. -/
@[reassoc] theorem coefficientShearFinalTerminalComponent_infinity_original (i : Fin 2) :
    ProjectiveLine.infinity K ≫
        coefficientShearFinalTerminalComponent hπ data D s hs hk hp i ≫ (G).hom =
      finalNodeSection hπ data D s hs hk hp (.inr ()) := by
  rw [coefficientShearFinalTerminalComponent_original, finalTerminalComponent_infinity]

/-- The complete ordered terminal component as a morphism over the residue field. -/
def coefficientShearFinalTerminalOverComponent (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (coefficientShearFinalTerminalComponent hπ data D s hs hk hp i)
    (coefficientShearFinalTerminalComponent_structure hπ data D s hs hk hp i)

end FLT.Mazur.WeierstrassDividedDepth
