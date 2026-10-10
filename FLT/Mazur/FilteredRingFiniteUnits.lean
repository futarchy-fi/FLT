/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingFiniteEqualities

/-!
# Lifting finitely many units in a filtered ring colimit

Lift values and inverses together, then detect their inverse equations at
one later stage. The construction works above any prescribed starting stage.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u v w

variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat)]

include hc in
/-- A finite family of colimit elements lifts above any specified stage. -/
theorem exists_lifts_of_finite {K : Type*} [Finite K] (i : I) (x : K → c.pt) :
    ∃ (j : I) (_ : i ⟶ j) (y : K → F.obj j), ∀ k, c.ι.app j (y k) = x k := by
  classical
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  choose j y hy using fun k ↦ Types.jointly_surjective_of_isColimit hc' (x k)
  cases nonempty_fintype K
  obtain ⟨a, ha⟩ := IsFiltered.sup_objs_exists (insert i (Finset.univ.image j))
  let f (k : K) : j k ⟶ a :=
    (ha (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩))).some
  refine ⟨a, (ha (Finset.mem_insert_self _ _)).some, fun k ↦ F.map (f k) (y k), ?_⟩
  intro k
  exact (congrArg (fun g : F.obj (j k) ⟶ c.pt ↦ g (y k)) (c.w (f k))).trans (hy k)

include hc in
/-- Finitely many actual units lift to actual units at one common later stage. -/
theorem exists_unit_lifts_of_finite {K : Type*} [Finite K] (i : I) (x : K → c.ptˣ) :
    ∃ (j : I) (_ : i ⟶ j) (y : K → (F.obj j)ˣ),
      ∀ k, Units.map (c.ι.app j).hom.toMonoidHom (y k) = x k := by
  classical
  obtain ⟨j, f, a, ha⟩ := exists_lifts_of_finite F c hc i
    (fun k : K × Bool ↦ if k.2 then (x k.1 : c.pt) else (↑(x k.1)⁻¹ : c.pt))
  have h (k : K) : c.ι.app j (a (k, true) * a (k, false)) = c.ι.app j 1 := by
    rw [map_mul, ha, ha, map_one]
    simp
  obtain ⟨l, g, hg⟩ := exists_map_eq_of_finite F c hc j
    (fun k ↦ a (k, true) * a (k, false)) (fun _ ↦ 1) h
  have hinv (k : K) : F.map g (a (k, true)) * F.map g (a (k, false)) = 1 := by
    simpa only [map_mul, map_one] using hg k
  let y (k : K) : (F.obj l)ˣ :=
    ⟨F.map g (a (k, true)), F.map g (a (k, false)), hinv k, by rw [mul_comm, hinv]⟩
  refine ⟨l, f ≫ g, y, fun k ↦ Units.ext ?_⟩
  change c.ι.app l (F.map g (a (k, true))) = (x k : c.pt)
  have he := congrArg (fun q : F.obj j ⟶ c.pt ↦ q (a (k, true))) (c.w g)
  exact he.trans (by simpa using ha (k, true))

end FLT.Mazur.Approximation
