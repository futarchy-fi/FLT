/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDisjointPullbackGluing

/-!
# Gluing restriction isomorphisms over a disjoint union

Local isomorphisms on disjoint opens give an actual isomorphism over their
union. No overlap compatibility or chosen global isomorphism is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.DisjointRestrictionIso

variable {X : Scheme} {M N : X.Modules}

/-- Restriction along a nested pair of opens. -/
def step (M : X.Modules) {V U : X.Opens} (h : V ≤ U) :
    M.restrict V.ι ≅ (M.restrict U.ι).restrict (X.homOfLE h) :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M

/-- Restrict an actual local isomorphism to a smaller open. -/
def shrink {V U : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ N.restrict U.ι) :
    M.restrict V.ι ≅ N.restrict V.ι :=
  step M h ≪≫ (restrictFunctor (X.homOfLE h)).mapIso e ≪≫ (step N h).symm

/-- Independent restriction isomorphisms assemble over the actual union open. -/
def glue {ι : Type} (V : ι → X.Opens)
    (hd : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (e : ∀ i, M.restrict (V i).ι ≅ N.restrict (V i).ι) :
    M.restrict (iSup V).ι ≅ N.restrict (iSup V).ι := by
  let D : X.Opens := iSup V
  let j (i : ι) : (V i).toScheme ⟶ D.toScheme := X.homOfLE (le_iSup V i)
  have hj : Pairwise (fun i k ↦ Disjoint (j i).opensRange (j k).opensRange) := by
    intro i k hik
    rw [← Opens.coe_disjoint]
    apply Set.disjoint_left.mpr
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    have hab : b.val = a.val := by
      simpa only [j, Scheme.homOfLE_apply] using congrArg Subtype.val hb
    exact (Set.disjoint_left.mp (Opens.coe_disjoint.mpr (hd hik)))
      a.property (hab ▸ b.property)
  have hc : ∀ x : D.toScheme, ∃ i, x ∈ Set.range (j i) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    refine ⟨i, ⟨x.val, hi⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply (le_iSup V i) ⟨x.val, hi⟩
  apply ModuleSheafDisjointPullbackGluing.glueIso (fun i ↦ (V i).toScheme) j hj hc
  intro i
  exact ((restrictFunctorIsoPullback (j i)).app _).symm ≪≫
    (step M (le_iSup V i)).symm ≪≫ e i ≪≫ step N (le_iSup V i) ≪≫
      (restrictFunctorIsoPullback (j i)).app _

end FLT.Mazur.DisjointRestrictionIso
