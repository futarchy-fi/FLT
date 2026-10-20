/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteFlatSourceExt
public import FLT.Mazur.WeierstrassDividedSecantSource

/-!
# Uniqueness of resolved secant outputs on flat refinements

The secant localization preserves flatness over the original coefficient
ring. Thus any flat scheme refinement has at most one finite-model output
with the prescribed secant contraction, even for nonreduced sources.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "T" => DividedSecantRing W s b3 b4 b6 a c

instance dividedSecantFlat [Module.Flat R S] : Module.Flat R T := by
  let _ : Module.Flat S T := IsLocalization.flat T
    (Submonoid.powers (a (x W s b3 b4 b6) - c (x W s b3 b4 b6)))
  exact Module.Flat.trans R S T

end FLT.Mazur.WeierstrassDilatation

namespace FLT.Mazur.WeierstrassDividedDepth
universe u
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open WeierstrassDilatation
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [Module.Flat R S] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "T" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "out" => dividedSecantOutput W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6
local notation "sec" => dividedSecantToCurve W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6

/-- Contraction detects secant outputs on every flat refinement of the actual source. -/
theorem finiteSecantOutput_ext {X : Scheme.{u}} (p : X ⟶ Spec (.of T)) [Flat p]
    (f g : X ⟶ finiteGlobalModel hπ data k hk)
    (hf : f ≫ finiteGlobalContraction hπ data k hk = p ≫ sec)
    (hg : g ≫ finiteGlobalContraction hπ data k hk = p ≫ sec) : f = g := by
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hs : (p ≫ Spec.map (CommRingCat.ofHom (out).toRingHom)) ≫
      WeierstrassIntegralChart.chartStructure W 2 =
        p ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [Category.assoc, WeierstrassIntegralChart.chartStructure,
      WeierstrassIntegralChart.specAlgHom_structure]
  let _ : Flat ((p ≫ Spec.map (CommRingCat.ofHom (out).toRingHom)) ≫
      WeierstrassIntegralChart.chartStructure W 2) := by
    rw [hs]
    infer_instance
  apply finiteGlobalContraction_ext_of_flat_source hπ data k hk
    (p ≫ Spec.map (CommRingCat.ofHom (out).toRingHom)) f g
  · simpa only [dividedSecantToCurve, Category.assoc] using hf
  · simpa only [dividedSecantToCurve, Category.assoc] using hg

end FLT.Mazur.WeierstrassDividedDepth
