/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAffineCoverDimension
public import FLT.Mazur.CoherentFreeSheaf
/-!
# Structure cohomology of a disjoint acyclic open cover

Mixed intersections are empty. Positive increasing Čech terms therefore
vanish, and acyclicity of the individual charts identifies Čech and sheaf
cohomology. No affineness of the charts is required.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.DisjointStructureCohomology
open FCurve CechSheafHZero CechAcyclicCokernel
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (hd : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
local instance : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _
include hd
/-- A tuple intersection is one chart or the empty open. -/
theorem intersection_cases (n : ℕ) (a : Fin (n + 1) → ι) :
    V U n a = U (a 0) ∨ V U n a = ⊥ := by
  classical
  by_cases h : ∀ j, a j = a 0
  · left
    simp only [V, h, iInf_const]
  · right
    obtain ⟨j, hj⟩ := not_forall.mp h
    apply le_bot_iff.mp
    calc
      V U n a ≤ U (a j) ⊓ U (a 0) := le_inf (iInf_le _ j) (iInf_le _ 0)
      _ = ⊥ := (hd hj).eq_bot
/-- Acyclic disjoint charts give acyclic tuple intersections. -/
theorem coverAcyclic
    (hU : ∀ i q, Subsingleton (ModuleH ((structureUnitModule X).restrict (U i).ι) (q + 1))) :
    CoverAcyclic U (structureAbelianSheaf X) := by
  intro n q a
  have hz : Subsingleton (ModuleH
      ((structureUnitModule X).restrict (Scheme.Opens.ι (V U n a))) (q + 1)) := by
    rcases intersection_cases U hd n a with he | he
    · rw [he]
      exact hU (a 0) q
    · rw [he]
      exact affineOpen_moduleH_succ_subsingleton _ _ (isAffineOpen_bot X) q
  exact ⟨fun x y ↦ (moduleOpenHEquiv (V U n a) (structureUnitModule X) (q + 1)).injective
    (hz.elim _ _)⟩
/-- Every positive increasing Čech term vanishes for disjoint charts. -/
theorem cech_positive [LinearOrder ι] (q : ℕ) :
    Subsingleton (CH U (structureAbelianSheaf X) (q + 1)) := by
  have hz (a : IncreasingCechComplex.Tuple (ι := ι) (q + 1)) : V U (q + 1) a.val = ⊥ := by
    apply le_bot_iff.mp
    calc
      V U (q + 1) a.val ≤ U (a.val 0) ⊓ U (a.val 1) := le_inf (iInf_le _ 0) (iInf_le _ 1)
      _ = ⊥ := (hd (ne_of_lt (a.property (by exact Fin.zero_lt_one)))).eq_bot
  have ht : Subsingleton (IncreasingCechComplex.Term U (structureAbelianSheaf X) (q + 1)) := by
    have (a : IncreasingCechComplex.Tuple (ι := ι) (q + 1)) :
        Subsingleton Γ(X, V U (q + 1) a.val) := by
      rw [hz a]
      infer_instance
    exact inferInstanceAs (Subsingleton (∀ a : IncreasingCechComplex.Tuple (ι := ι) (q + 1),
      Γ(X, V U (q + 1) a.val)))
  have hterm : IsZero ((IncreasingCechComplex.complex U (structureAbelianSheaf X)).X (q + 1)) :=
    AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of
      (IncreasingCechComplex.Term U (structureAbelianSheaf X) (q + 1)))
  have hhom := ((IncreasingCechComplex.complex U (structureAbelianSheaf X)).sc
    (q + 1)).isZero_homology_of_isZero_X₂ hterm
  exact AddCommGrpCat.subsingleton_of_isZero
    (hhom.of_iso (CechSortingHomotopy.homologyIso U (structureAbelianSheaf X) (q + 1)))
/-- A disjoint cover with acyclic structure modules is acyclic. -/
theorem positive [LinearOrder ι] (hCover : iSup U = ⊤)
    (hU : ∀ i q, Subsingleton (ModuleH ((structureUnitModule X).restrict (U i).ι) (q + 1)))
    (q : ℕ) : Subsingleton (ModuleH (structureUnitModule X) (q + 1)) := by
  have := cech_positive U hd q
  exact (moduleCechEquiv (structureUnitModule X) U hCover
    (coverAcyclic U hd hU) (q + 1)).symm.injective.subsingleton
end FLT.Mazur.DisjointStructureCohomology
