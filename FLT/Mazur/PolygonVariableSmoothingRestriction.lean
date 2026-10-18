/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonVariableSmoothingFamily
public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Coefficient restrictions of the variable-smoothing target

The original coefficient homomorphism acts on every full node ring. Its
puncture squares descend to a single map of the complete cyclic schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonVariableSmoothing
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (n : ℕ) (t : Fin n → R) (s : Fin n → S)
  [∀ i, Fact (IsNilpotent (t i))] [∀ i, Fact (IsNilpotent (s i))]
  (hs : ∀ i, f (t i) = s i) (h : 2 ≤ n)

/-- The complete target projection uses the specified coefficient map at every node. -/
def parameterProjection : scheme S n s h ⟶ scheme R n t h :=
  desc S n s h
    (fun i ↦ Spec.map (CommRingCat.ofHom (ringMap f (t i) (s i) (hs i))) ≫
      chart R n t h i) (by
        intro i
        rw [← Category.assoc, leftBranchOpen_ringMap, Category.assoc, overlap,
          precedingBranch_ringMap_assoc])

/-- Every full chart square retains the actual coefficient substitution. -/
@[reassoc] theorem chart_parameterProjection (i : Fin n) :
    chart S n s h i ≫ parameterProjection f n t s hs h =
      Spec.map (CommRingCat.ofHom (ringMap f (t i) (s i) (hs i))) ≫ chart R n t h i :=
  chart_desc S n s h _ _ i

/-- The complete projection lies over the original coefficient spectrum map. -/
@[reassoc] theorem parameterProjection_base :
    parameterProjection f n t s hs h ≫ toBase R n t h =
      toBase S n s h ≫ Spec.map (CommRingCat.ofHom f) := by
  apply (chartCover S n s h).hom_ext
  intro i
  change chart S n s h i ≫ _ = chart S n s h i ≫ _
  rw [chart_parameterProjection_assoc, chart_toBase, chart_toBase_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r
  exact ringMap_scalar f (t i) (s i) (hs i) r

end FLT.Mazur.PolygonVariableSmoothing
