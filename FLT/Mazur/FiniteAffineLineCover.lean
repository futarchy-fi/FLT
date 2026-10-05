/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTrivialLineSectionOpen
public import FLT.Mazur.AffineCoverIntersections

/-!
# Finite affine trivializing covers of a line sheaf

Compactness makes a line-trivializing affine cover finite. On a separated
scheme each nonempty tuple intersection is affine and still trivializes the
line, supplying the charts required by the finite Cech argument.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {L : X.Modules}

/-- Every line sheaf on a compact scheme has a finite affine trivializing cover. -/
theorem LocallyFreeRankOne.finite_affine_trivializing_cover [CompactSpace X]
    (hL : LocallyFreeRankOne L) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty (L.restrict (U i).ι ≅ structureModule (U i).toScheme)) ∧
      iSup U = ⊤ := by
  classical
  choose U hx hU e using hL.exists_affine_trivialization
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨t, inferInstance, fun i ↦ U i, fun i ↦ hU i, fun i ↦ e i, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

/-- A trivialization restricts to every smaller ambient open. -/
def lineTrivializationOfLE {U V : X.Opens} (h : V ≤ U)
    (e : L.restrict U.ι ≅ structureModule U.toScheme) :
    L.restrict V.ι ≅ structureModule V.toScheme :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app L ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app L ≪≫
      (restrictFunctor (X.homOfLE h)).mapIso e ≪≫ restrictUnitIso (X.homOfLE h)

/-- Every Cech tuple intersection inherits a trivialization from its first member. -/
def tupleLineTrivialization {ι : Type u} (U : ι → X.Opens)
    (e : ∀ i, L.restrict (U i).ι ≅ structureModule (U i).toScheme)
    (q : ℕ) (a : Fin (q + 1) → ι) :
    L.restrict (Scheme.Opens.ι (CechSheafHZero.V U q a)) ≅
      structureModule (Scheme.Opens.toScheme (CechSheafHZero.V U q a)) :=
  lineTrivializationOfLE (show CechSheafHZero.V U q a ≤ U (a 0) from iInf_le _ 0) (e (a 0))

end FLT.Mazur.FCurve
