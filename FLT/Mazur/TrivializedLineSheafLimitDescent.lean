/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CocycleSheafLimitDescent
public import FLT.Mazur.LineTrivializationCocycleRecovery

/-!
# Descending a specified trivialized line sheaf

Use the genuine transition cocycle of the given local trivializations, descend
it through the inverse system, and recover the original sheaf by pullback.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- A specified line sheaf descends once a finite trivializing atlas exists at a stage. -/
theorem exists_trivializedLineSheaf_of_limit {ι : Type u} [Finite ι]
    (i : I) (U : ι → (D.obj i).Opens) (hcover : iSup U = ⊤)
    (hcompact : ∀ s, IsCompact (finiteIntersectionOpen U s : Set (D.obj i)))
    (L : c.pt.Modules)
    (e : ∀ j, Nonempty (L.restrict (c.π.app i ⁻¹ᵁ U j).ι ≅
      structureModule (c.π.app i ⁻¹ᵁ U j).toScheme)) :
    ∃ (r : Over i) (M : (D.obj r.left).Modules), LocallyFreeRankOne M ∧
      Nonempty ((Scheme.Modules.pullback (c.π.app r.left)).obj M ≅ L) := by
  let e' j := Classical.choice (e j)
  obtain ⟨r, M, hM, ⟨eM⟩⟩ := exists_cocycleSheaf_of_limit D c hc i U hcover hcompact
    (lineTrivializationCocycle e')
  exact ⟨r, M, hM, ⟨eM ≪≫ lineTrivializationCocycleIso e'
    ((c.π.app i).iSup_preimage_eq_top hcover)⟩⟩

end FLT.Mazur.Approximation
