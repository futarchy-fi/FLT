/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalFamily
public import FLT.Mazur.PolygonSmoothingSpecialBranches

/-!
# The original cyclic polygon is the zero-parameter assembled family

The actual split-node comparison extends to the complete cyclic diagrams and
hence to their colimits. Both branch embeddings and the arithmetic base are
retained by this identification, including the two-gon's two edges.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

set_option backward.isDefEq.respectTransparency false

open PolygonSmoothing

variable (K : Type u) [Field K] (n : ℕ)

instance zeroParameter_nilpotent : Fact (IsNilpotent (0 : K)) := ⟨1, by simp⟩

/-- The original node comparison extends over all cyclic edges. -/
def zeroDiagramIso : PolygonCyclicAtlas.diagram K n ≅ diagram K 0 n :=
  NatIso.ofComponents (fun j ↦ match j with
    | .left _ => Iso.refl _
    | .right _ => specialFiberIso K) (by
      intro i j f
      cases f with
      | id i => simp
      | fst i =>
        change PolygonNodeBranches.left K ≫ (specialFiberIso K).hom =
          𝟙 _ ≫ leftBranchOpen K 0
        rw [Category.id_comp, specialFiberIso_left]
      | snd i =>
        change ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K) ≫
          (specialFiberIso K).hom = 𝟙 _ ≫ precedingBranch K 0
        rw [Category.id_comp, Category.assoc, specialFiberIso_right]
        rfl)

variable (h : 2 ≤ n)

/-- The actual assembled zero-parameter scheme is the original cyclic polygon. -/
def zeroFiberIso : PolygonCyclicAtlas.scheme K n h ≅ scheme K 0 n h :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  HasColimit.isoOfNatIso (zeroDiagramIso K n)

/-- The global comparison retains the original node chart embeddings exactly. -/
@[reassoc] theorem chart_zeroFiberIso (i : Fin n) :
    PolygonCyclicAtlas.chart K n h i ≫ (zeroFiberIso K n h).hom =
      (specialFiberIso K).hom ≫ chart K 0 n h i := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact HasColimit.ι_isoOfNatIso_hom (zeroDiagramIso K n) (.right i)

/-- The zero-fiber identification preserves the original polygon's structure map. -/
@[reassoc] theorem zeroFiberIso_base :
    (zeroFiberIso K n h).hom ≫ toBase K 0 n h = PolygonCyclicAtlas.toBase K n h := by
  let : Fact (2 ≤ n) := ⟨h⟩
  have hi (i : Fin n) :
      PolygonCyclicAtlas.chart K n h i ≫ (zeroFiberIso K n h).hom ≫ toBase K 0 n h =
        PolygonCyclicAtlas.chart K n h i ≫ PolygonCyclicAtlas.toBase K n h := by
    rw [chart_zeroFiberIso_assoc, chart_toBase, PolygonCyclicAtlas.chart_toBase]
    exact specialFiberIso_base K
  apply colimit.hom_ext
  intro j
  cases j with
  | right i => exact hi i
  | left i =>
    have hw := colimit.w (PolygonCyclicAtlas.diagram K n) (WalkingMultispan.Hom.fst i)
    rw [← hw]
    change (PolygonNodeBranches.left K ≫ PolygonCyclicAtlas.chart K n h i) ≫ _ =
      (PolygonNodeBranches.left K ≫ PolygonCyclicAtlas.chart K n h i) ≫ _
    simp only [Category.assoc, hi]

end FLT.Mazur.PolygonInfinitesimal
