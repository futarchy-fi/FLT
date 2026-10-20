/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentFlatSourceExt
public import FLT.Mazur.WeierstrassDividedTangentSecantScheme

/-!
# Resolved tangent and secant outputs agree at independent target depths

The original formulas agree over the same input source. Flat-source
uniqueness then identifies their actual finite-model lifts, including
outputs above the original singular point and nonreduced overlaps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [Module.Flat R S] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n k m : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (d : Data W π m) (a c : Coordinate W (π ^ m) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ m
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "it" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "iv" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "tan" => dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6
local notation "sec" => dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Actual lifts of the two original formulas agree on every common flat tangent refinement. -/
theorem finiteReindexedTangentSecantOutput_ext {X : Scheme.{u}}
    (p : X ⟶ Spec (.of T)) (q : X ⟶ Spec (.of V)) [Flat p]
    (hpq : p ≫ it = q ≫ iv)
    (f g : X ⟶ finiteGlobalModel hπ data k hk)
    (hf : f ≫ finiteGlobalContraction hπ data k hk = p ≫ tan)
    (hg : g ≫ finiteGlobalContraction hπ data k hk = q ≫ sec) : f = g := by
  apply finiteTangentOutput_ext hπ data hk d a c p f g hf
  rw [hg]
  exact (dividedTangentSecant_scheme W s d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6 p q hpq).symm

end FLT.Mazur.WeierstrassDividedDepth
