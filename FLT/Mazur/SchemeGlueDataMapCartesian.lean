/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeGlueDataMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Cartesian charts of a map between glued schemes

Cartesian overlap squares force exact inverse images of whole chart
images. Consequently every chart square of the global map is cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u

variable (D E : Scheme.GlueData.{u}) (c : E.J → D.J)
  (f : ∀ i, E.U i ⟶ D.U (c i))
  (g : ∀ i j, E.V (i, j) ⟶ D.V (c i, c j))
  (hf : ∀ i j, g i j ≫ D.f (c i) (c j) = E.f i j ≫ f i)
  (ht : ∀ i j, g i j ≫ D.t (c i) (c j) = E.t i j ≫ g j i)
  (hp : ∀ i j, IsPullback (g i j) (E.f i j) (D.f (c i) (c j)) (f i))

include hp in
/-- Every whole source chart is exactly the inverse image of its target chart. -/
theorem schemeGlueDataMap_preimage (i : E.J) :
    schemeGlueDataMap D E c f g hf ht ⁻¹' Set.range (D.ι (c i)) = Set.range (E.ι i) := by
  ext z
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨j, w, rfl⟩ := E.ι_jointly_surjective z
    have he : D.ι (c j) (f j w) = D.ι (c i) v := by
      rw [← Scheme.Hom.comp_apply, ← schemeGlueDataMap_chart D E c f g hf ht j]
      exact hv.symm
    obtain ⟨q, hq, _⟩ := (D.ι_eq_iff (c j) (c i) (f j w) v).mp he
    obtain ⟨r, _hr, hw⟩ := Scheme.exists_preimage_of_isPullback (hp j i) q w hq
    refine ⟨(E.t j i ≫ E.f i j) r, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, E.glue_condition]
    rw [Scheme.Hom.comp_apply, hw]
  · rintro ⟨w, rfl⟩
    refine ⟨f i w, ?_⟩
    exact congrArg (fun k : E.U i ⟶ D.glued ↦ k w)
      (schemeGlueDataMap_chart D E c f g hf ht i).symm

include hp in
/-- Cartesian overlap squares glue to a cartesian square on every whole chart. -/
theorem schemeGlueDataMap_isPullback (i : E.J) :
    IsPullback (f i) (E.ι i) (D.ι (c i)) (schemeGlueDataMap D E c f g hf ht) := by
  apply IsOpenImmersion.isPullback
  · exact schemeGlueDataMap_chart D E c f g hf ht i
  · ext z
    exact Set.ext_iff.mp (schemeGlueDataMap_preimage D E c f g hf ht hp i) z

include hp hf ht in
/-- The cartesian criterion applies to any global map with the prescribed chart restrictions. -/
theorem schemeGlueDataMap_isPullback_of_charts (q : E.glued ⟶ D.glued)
    (hq : ∀ i, E.ι i ≫ q = f i ≫ D.ι (c i)) (i : E.J) :
    IsPullback (f i) (E.ι i) (D.ι (c i)) q := by
  have heq : q = schemeGlueDataMap D E c f g hf ht :=
    schemeGlueData_hom_ext E _ _ (fun j ↦ (hq j).trans
      (schemeGlueDataMap_chart D E c f g hf ht j).symm)
  rw [heq]
  exact schemeGlueDataMap_isPullback D E c f g hf ht hp i

end FLT.Mazur
