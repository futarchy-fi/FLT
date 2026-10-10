/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Full ideals across ambient open immersions

A finite family in an open of a separated ambient extends as an actual closed
family. Restriction recovers the full ideal. Conversely a closed family whose
support lies in the open is recovered by extension of its restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.OpenIdealCover

variable {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]

/-- A finite family in an ambient open remains closed in a separated containing ambient. -/
theorem finiteFamily_closed (p : Y ⟶ S) [IsSeparated p] (J : X.IdealSheafData)
    [IsFinite (J.subschemeι ≫ i ≫ p)] : IsClosedImmersion (J.subschemeι ≫ i) := by
  have : IsFinite ((J.subschemeι ≫ i) ≫ p) := by
    simpa only [Category.assoc] using
      (inferInstance : IsFinite (J.subschemeι ≫ i ≫ p))
  have := IsFinite.of_comp (J.subschemeι ≫ i) p
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

/-- Restriction recovers the whole ideal of an open family whose extension is closed. -/
theorem open_comap_map (J : X.IdealSheafData) [IsClosedImmersion (J.subschemeι ≫ i)] :
    (J.map i).comap i = J := by
  let q : IsPullback J.subschemeι (𝟙 J.subscheme) i (J.subschemeι ≫ i) :=
    IsPullback.of_vert_isIso_mono ⟨(Category.id_comp _).symm⟩
  rw [map, ← ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso q.isoPullback.hom, q.isoPullback_hom_fst,
    ker_subschemeι]

/-- Extension recovers the whole ideal when the actual closed family lies in the open. -/
theorem open_map_comap (J : Y.IdealSheafData)
    (h : Set.range J.subschemeι ⊆ Set.range i) : (J.comap i).map i = J := by
  let f := IsOpenImmersion.lift i J.subschemeι h
  have hf : f ≫ i = J.subschemeι := IsOpenImmersion.lift_fac _ _ _
  let q : IsPullback f (𝟙 J.subscheme) i J.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨hf.trans (Category.id_comp _).symm⟩
  have he : J.comap i = f.ker := by
    rw [comap, ← Scheme.Hom.ker_comp_of_isIso q.isoPullback.hom, q.isoPullback_hom_fst]
  rw [he, map_ker, hf, ker_subschemeι]

omit [IsOpenImmersion i] in
/-- Extension of a closed open family has its entire support inside the open. -/
theorem open_map_range (J : X.IdealSheafData) [IsClosedImmersion (J.subschemeι ≫ i)] :
    Set.range (J.map i).subschemeι ⊆ Set.range i := by
  change Set.range (J.subschemeι ≫ i).imageι ⊆ Set.range i
  rintro _ ⟨x, rfl⟩
  obtain ⟨z, rfl⟩ := (J.subschemeι ≫ i).toImage.surjective x
  exact ⟨J.subschemeι z,
    (congrArg (fun f ↦ f z) (Scheme.Hom.toImage_imageι (J.subschemeι ≫ i))).symm⟩

end FLT.Mazur.OpenIdealCover
