/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Full ideal correspondence for a closed ambient immersion

Ideals on a closed subscheme correspond to ideals of the original ambient
scheme containing its kernel. Both inverse laws are proved using actual
cartesian closed immersions and retain the full ideal sheaf structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]

/-- Pushforward along a closed ambient immersion and pullback recover the full original ideal. -/
theorem closed_comap_map (J : X.IdealSheafData) : (J.map i).comap i = J := by
  let q : IsPullback J.subschemeι (𝟙 J.subscheme) i (J.subschemeι ≫ i) :=
    IsPullback.of_vert_isIso_mono ⟨(Category.id_comp _).symm⟩
  rw [map, ← ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso q.isoPullback.hom, q.isoPullback_hom_fst,
    ker_subschemeι]

/-- Pullback of a containing ideal and pushforward recover the entire ambient ideal. -/
theorem closed_map_comap (J : Y.IdealSheafData) (h : i.ker ≤ J) :
    (J.comap i).map i = J := by
  let f := IsClosedImmersion.lift i J.subschemeι (by simpa only [ker_subschemeι] using h)
  have hf : f ≫ i = J.subschemeι := IsClosedImmersion.lift_fac _ _ _
  let q : IsPullback f (𝟙 J.subscheme) i J.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨hf.trans (Category.id_comp _).symm⟩
  have he : J.comap i = f.ker := by
    rw [comap, ← Scheme.Hom.ker_comp_of_isIso q.isoPullback.hom, q.isoPullback_hom_fst]
  rw [he, map_ker, hf, ker_subschemeι]

/-- Actual ideals on a closed ambient scheme correspond to containing ideals upstairs. -/
def closedIdealEquiv : X.IdealSheafData ≃ { J : Y.IdealSheafData // i.ker ≤ J } where
  toFun J := ⟨J.map i, Scheme.Hom.le_ker_comp _ _⟩
  invFun J := J.val.comap i
  left_inv := closed_comap_map i
  right_inv J := Subtype.ext (closed_map_comap i J.val J.property)

/-- The correspondence remembers the closed subscheme projection to the original ambient. -/
theorem closedIdealEquiv_ideal (J : X.IdealSheafData) :
    (closedIdealEquiv i J).val = (J.subschemeι ≫ i).ker := rfl

end FLT.Mazur.ClosedIdealCover
