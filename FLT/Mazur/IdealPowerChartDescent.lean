/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerExtensionCharts
public import FLT.Mazur.CoherentSubmoduleUnion

/-!
# Descent and overlap transport of ideal-power chart extensions

Canonical restriction comparisons descend spectrum maps to affine opens and
carry their comparison squares to actual geometric intersections.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility
open FLT.Mazur.IdealPowerExtensionCharts FLT.Mazur.CoherentSubmoduleEnlargement
open FLT.Mazur.CoherentSubmoduleUnion (along)
open FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts

universe u

namespace FLT.Mazur.IdealPowerChartDescent

variable {X Y Z : Scheme.{u}}

/-- Transport a chart map through a factorization of its open immersion. -/
def transportMap (k : Z ⟶ Y) (j : Y ⟶ X) (l : Z ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion l] (h : k ≫ j = l)
    {P Q : X.Modules} (f : P.restrict j ⟶ Q.restrict j) :
    P.restrict l ⟶ Q.restrict l :=
  (along k j l h).hom.app P ≫ (restrictFunctor k).map f ≫ (along k j l h).inv.app Q

/-- Transport of a restricted global map is its direct restriction. -/
lemma transportMap_map (k : Z ⟶ Y) (j : Y ⟶ X) (l : Z ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion l] (h : k ≫ j = l)
    {P Q : X.Modules} (f : P ⟶ Q) :
    transportMap k j l h ((restrictFunctor j).map f) = (restrictFunctor l).map f := by
  unfold transportMap
  rw [← Functor.comp_map, ← Category.assoc, ← (along k j l h).hom.naturality]
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Transport preserves composition. -/
lemma transportMap_comp (k : Z ⟶ Y) (j : Y ⟶ X) (l : Z ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion l] (h : k ≫ j = l)
    {P Q R : X.Modules} (f : P.restrict j ⟶ Q.restrict j)
    (g : Q.restrict j ⟶ R.restrict j) :
    transportMap k j l h (f ≫ g) = transportMap k j l h f ≫ transportMap k j l h g := by
  simp [transportMap, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 800000 in
-- Expanding the nested restriction functors needs additional module-structure reduction.
/-- Transport carries the original comparison square through any open factorization. -/
lemma transportMap_comparison (k : Z ⟶ Y) (j : Y ⟶ X) (l : Z ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion l] (h : k ≫ j = l)
    (U : X.Opens) {P Q : X.Modules}
    (f : P.restrict j ⟶ Q.restrict j) (g : P.restrict U.ι ⟶ Q.restrict U.ι)
    (hf : (restrictFunctor (j ⁻¹ᵁ U).ι).map f = pullComparison j U g) :
    (restrictFunctor (l ⁻¹ᵁ U).ι).map (transportMap k j l h f) =
      pullComparison l U g := by
  subst l
  let r := k ∣_ (j ⁻¹ᵁ U)
  let F := restrictFunctor ((k ≫ j) ⁻¹ᵁ U).ι
  let G := restrictFunctor r
  let A := along k j (k ≫ j) rfl
  let B := (restrictFunctorComp ((k ≫ j) ⁻¹ᵁ U).ι k).symm ≪≫
    along r (j ⁻¹ᵁ U).ι (((k ≫ j) ⁻¹ᵁ U).ι ≫ k) (morphismRestrict_ι k (j ⁻¹ᵁ U))
  let C := along r (j ∣_ U) ((k ≫ j) ∣_ U) (morphismRestrict_comp k j U).symm
  have hc (M : X.Modules) :
      F.map (A.hom.app M) ≫ B.hom.app (M.restrict j) ≫
        G.map ((restrictionSquare j U).inv.app M) =
      (restrictionSquare (k ≫ j) U).inv.app M ≫ C.hom.app (M.restrict U.ι) := by
    apply Scheme.Modules.hom_ext
    intro T
    simp only [A, B, C, F, G, along, restrictionSquare, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Hom.comp_app,
      restriction_app, restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app,
      restrictFunctorCongr_inv_app_app,
      restrict_map, ← Functor.map_comp]
    congr 1
  have hn := B.hom.naturality f
  simp only [Functor.comp_map] at hn
  change F.map ((restrictFunctor k).map f) ≫ B.hom.app (Q.restrict j) =
    B.hom.app (P.restrict j) ≫ G.map ((restrictFunctor (j ⁻¹ᵁ U).ι).map f) at hn
  rw [hf] at hn
  have hg := C.hom.naturality g
  simp only [Functor.comp_map] at hg
  have hcQ := hc Q
  apply (cancel_mono (F.map (A.hom.app Q) ≫ B.hom.app (Q.restrict j) ≫
    G.map ((restrictionSquare j U).inv.app Q))).mp
  change F.map (A.hom.app P ≫ (restrictFunctor k).map f ≫ A.inv.app Q) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc (A.inv.app Q) (A.hom.app Q),
    Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rw [reassoc_of% hn]
  simp only [pullComparison, Functor.map_comp, Category.assoc]
  rw [← G.map_comp ((restrictionSquare j U).hom.app Q),
    Iso.hom_inv_id_app, G.map_id]
  erw [Category.comp_id]
  erw [← Category.assoc, ← Category.assoc, hc P, Category.assoc, ← hg]
  rw [hcQ]
  simp only [Iso.hom_inv_id_app_assoc]

/-- Restrict a map on an ambient open to a smaller ambient open. -/
def onOpen {P Q : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (f : P.restrict U.ι ⟶ Q.restrict U.ι) : P.restrict V.ι ⟶ Q.restrict V.ι :=
  transportMap (X.homOfLE h) U.ι V.ι (X.homOfLE_ι h) f

/-- The ambient-open transport uses the canonical nested-restriction comparison. -/
lemma onOpen_nested {P Q : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (f : P.restrict U.ι ⟶ Q.restrict U.ι) :
    onOpen h f = (nestedRestriction h).inv.app P ≫
      (restrictFunctor (X.homOfLE h)).map f ≫ (nestedRestriction h).hom.app Q := by
  rfl

/-- Restricting a global map through an intermediate open is direct restriction. -/
lemma onOpen_map {P Q : X.Modules} {U V : X.Opens} (h : V ≤ U) (f : P ⟶ Q) :
    onOpen h ((restrictFunctor U.ι).map f) = (restrictFunctor V.ι).map f :=
  transportMap_map _ _ _ _ f

/-- Ambient-open transport preserves composition. -/
lemma onOpen_comp {P Q R : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (f : P.restrict U.ι ⟶ Q.restrict U.ι) (g : Q.restrict U.ι ⟶ R.restrict U.ι) :
    onOpen h (f ≫ g) = onOpen h f ≫ onOpen h g := transportMap_comp _ _ _ _ f g

/-- A comparison square restricts to the same original comparison on any subopen. -/
lemma onOpen_comparison {P Q : X.Modules} (U : X.Opens) {V W : X.Opens} (h : W ≤ V)
    (f : P.restrict V.ι ⟶ Q.restrict V.ι) (g : P.restrict U.ι ⟶ Q.restrict U.ι)
    (hf : (restrictFunctor (V.ι ⁻¹ᵁ U).ι).map f = pullComparison V.ι U g) :
    (restrictFunctor (W.ι ⁻¹ᵁ U).ι).map (onOpen h f) = pullComparison W.ι U g :=
  transportMap_comparison _ _ _ _ U f g hf

/-- The two actual geometric overlap maps agree on the comparison open. -/
lemma overlap_agreement {P Q : X.Modules} (U V W : X.Opens)
    (f : P.restrict V.ι ⟶ Q.restrict V.ι) (f' : P.restrict W.ι ⟶ Q.restrict W.ι)
    (g : P.restrict U.ι ⟶ Q.restrict U.ι)
    (hf : (restrictFunctor (V.ι ⁻¹ᵁ U).ι).map f = pullComparison V.ι U g)
    (hf' : (restrictFunctor (W.ι ⁻¹ᵁ U).ι).map f' = pullComparison W.ι U g) :
    (restrictFunctor ((V ⊓ W).ι ⁻¹ᵁ U).ι).map (onOpen inf_le_left f) =
      (restrictFunctor ((V ⊓ W).ι ⁻¹ᵁ U).ι).map (onOpen inf_le_right f') := by
  rw [onOpen_comparison U inf_le_left f g hf, onOpen_comparison U inf_le_right f' g hf']

/-- Descend the constructed spectrum extensions to the actual affine opens. -/
theorem exists_open_extensions [IsNoetherian X] (I : X.IdealSheafData) (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (g : M.restrict (complement I).ι ⟶ N.restrict (complement I).ι) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.affineOpens),
      (⨆ i, (V i).1) = ⊤ ∧ ∃ n : ℕ, ∃ f : ∀ i,
        (power I n M).restrict (V i).1.ι ⟶ N.restrict (V i).1.ι,
        ∀ i, (restrictFunctor ((V i).1.ι ⁻¹ᵁ complement I).ι).map (f i) =
          pullComparison (V i).1.ι (complement I)
            ((restrictFunctor (complement I).ι).map (inclusion (I ^ n) M) ≫ g) := by
  obtain ⟨ι, hι, V, hV, n, hn⟩ := exists_cover_extensions I M N g
  choose f hf using hn
  refine ⟨ι, hι, V, hV, n, fun i ↦ transportMap (V i).2.isoSpec.hom
    (V i).2.fromSpec (V i).1.ι (V i).2.isoSpec_hom_fromSpec (f i), fun i ↦ ?_⟩
  apply transportMap_comparison
  rw [pullComparison_comp, pullComparison_map]
  exact hf i

/-- The chosen affine-open extensions come with constructed overlap maps and their equality. -/
theorem exists_overlap_extensions [IsNoetherian X] (I : X.IdealSheafData) (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (g : M.restrict (complement I).ι ⟶ N.restrict (complement I).ι) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.affineOpens),
      (⨆ i, (V i).1) = ⊤ ∧ ∃ n : ℕ, ∃ f : ∀ i,
        (power I n M).restrict (V i).1.ι ⟶ N.restrict (V i).1.ι,
        (∀ i, (restrictFunctor ((V i).1.ι ⁻¹ᵁ complement I).ι).map (f i) =
          pullComparison (V i).1.ι (complement I)
            ((restrictFunctor (complement I).ι).map (inclusion (I ^ n) M) ≫ g)) ∧
        ∀ i j, (restrictFunctor (complement (I.comap ((V i).1 ⊓ (V j).1).ι)).ι).map
          (onOpen inf_le_left (f i)) =
          (restrictFunctor (complement (I.comap ((V i).1 ⊓ (V j).1).ι)).ι).map
            (onOpen inf_le_right (f j)) := by
  obtain ⟨ι, hι, V, hV, n, f, hf⟩ := exists_open_extensions I M N g
  refine ⟨ι, hι, V, hV, n, f, hf, fun i j ↦ ?_⟩
  rw [complement_comap]
  exact overlap_agreement (complement I) (V i).1 (V j).1 (f i) (f j) _ (hf i) (hf j)

end FLT.Mazur.IdealPowerChartDescent
