/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineSheaf
public import FLT.Mazur.SectionLineChartOverlap

/-!
# Coherent changes of chart for actual section-line sheaves

Changing the invertible coordinate preserves the inclusion in the ambient
sheaf. These comparisons are uniquely determined by that inclusion and
satisfy the identity and cocycle laws. In the coordinate trivializations,
they are multiplication by the constructed overlap unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
variable {R : Type u} [CommRing R] {ι : Type u}

/-- Change of invertible coordinate on the same actual line submodule. -/
def sheafChartChange (i j : ι) (L : Chart R ι i) (M : Chart R ι j)
    (h : L.val = M.val) : sheaf i L ≅ sheaf j M :=
  (tilde.functor (.of R)).mapIso (LinearEquiv.ofEq L.val M.val h).toModuleIso

/-- The chart change preserves the original ambient inclusion. -/
lemma sheafChartChange_inclusion (i j : ι) (L : Chart R ι i) (M : Chart R ι j)
    (h : L.val = M.val) :
    (sheafChartChange i j L M h).hom ≫ sheafInclusion j M = sheafInclusion i L := by
  change (tilde.functor (.of R)).map _ ≫ (tilde.functor (.of R)).map _ = _
  rw [← Functor.map_comp]
  congr 1

/-- An ambient-preserving comparison between two chart lines is unique. -/
lemma sheafChartChange_unique (i j : ι) (L : Chart R ι i) (M : Chart R ι j)
    (h : L.val = M.val) (a : sheaf i L ⟶ sheaf j M)
    (ha : a ≫ sheafInclusion j M = sheafInclusion i L) :
    a = (sheafChartChange i j L M h).hom := by
  apply (cancel_mono (sheafInclusion j M)).mp
  rw [ha, sheafChartChange_inclusion]

/-- The chart comparison on a repeated chart is the identity. -/
lemma sheafChartChange_refl (i : ι) (L : Chart R ι i) :
    sheafChartChange i i L L rfl = Iso.refl _ := by
  apply Iso.ext
  exact (sheafChartChange_unique i i L L rfl (𝟙 _) (Category.id_comp _)).symm

/-- Actual sheaf chart comparisons satisfy the cocycle law. -/
lemma sheafChartChange_cocycle (i j k : ι) (L : Chart R ι i) (M : Chart R ι j)
    (N : Chart R ι k) (h : L.val = M.val) (h' : M.val = N.val) :
    sheafChartChange i j L M h ≪≫ sheafChartChange j k M N h' =
      sheafChartChange i k L N (h.trans h') := by
  apply Iso.ext
  apply sheafChartChange_unique
  simp only [Iso.trans_hom, Category.assoc, sheafChartChange_inclusion]

/-- In coordinate frames the transition is multiplication by the actual overlap unit. -/
lemma sheafChartChange_trivialization (i j : ι) (L : Chart R ι i) (M : Chart R ι j)
    (h : L.val = M.val) :
    (sheafChartChange i j L M h).hom ≫ (sheafTrivialization j M).hom =
      (sheafTrivialization i L).hom ≫
        (tilde.functor (.of R)).map (ModuleCat.ofHom
          (LinearMap.toSpanSingleton R R (transitionUnit R ι i j L M h : R))) := by
  change (tilde.functor (.of R)).map _ ≫ (tilde.functor (.of R)).map _ =
    (tilde.functor (.of R)).map _ ≫ (tilde.functor (.of R)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact congrFun (eq_smul_generator R ι i L v) j

end FLT.Mazur.NormalizedSectionLine
