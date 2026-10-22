/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredFiniteModuleFlatDescent

/-!
# One flat coefficient stage for finitely many finitely presented modules

The modules can have different finite presentations. Flatness of their actual
colimit scalar extensions yields one common refinement where every module,
with every relation, is flat. All further transitions retain this property.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.Approximation
universe u v w z
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat)]

include hc in
/-- All relations in finitely many original finite modules become flat at one common stage. -/
theorem exists_flat_finite_module_family_stage {T : Type*} [Finite T]
    (i : I) (M : T → Type z) [∀ t, AddCommGroup (M t)] [∀ t, Module (F.obj i) (M t)]
    [∀ t, Module.FinitePresentation (F.obj i) (M t)]
    (h : ∀ t, ScalarFlat (c.ι.app i).hom (M t)) :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k) (t : T),
      ScalarFlat (F.map (g ≫ e)).hom (M t) := by
  classical
  let _ := Fintype.ofFinite T
  choose j g hg using fun t ↦ exists_flat_finite_module_stage F c hc i (M t) (h t)
  let A (t : T) : Under i := Under.mk (g t)
  obtain ⟨B, hB⟩ := IsFiltered.sup_objs_exists (Finset.univ.image A)
  refine ⟨B.right, B.hom, fun k e t ↦ ?_⟩
  let a : A t ⟶ B := (hB (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)).some
  have ha : g t ≫ a.right = B.hom := Under.w a
  simpa only [← Category.assoc, ha] using hg t k (a.right ≫ e)

end FLT.Mazur.Approximation
