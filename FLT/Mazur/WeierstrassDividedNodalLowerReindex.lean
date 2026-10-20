/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalLowerSmooth

/-!
# Shallow outputs with an independently indexed target datum

An explicit equality of depths transports the actual algebra map and its
contraction. This keeps finite-family indices out of coordinate-ring casts.
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
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {m k l : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 2 * k ≤ m)
  (hm : m ≤ 3 * k) (e : Data W π l) (hl : l = m - 2 * k)
  (a2 : R) (h2 : W.a₂ = π ^ (m - 2 * k) * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S) [Module.Flat R S]
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "res" => dividedTangentBranchRestriction W (π ^ k) d.b3 d.b4 d.b6 a c

/-- Transport the constructed algebra map to an independently indexed target datum. -/
def nodalLowerReindexedOutput : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] B := by
  subst l
  exact nodalLowerOutput D d hdepth hm e a2 h2 a c

/-- The transported map gives an actual target chart morphism. -/
def nodalLowerReindexedLift : Spec (.of B) ⟶ chart e :=
  Spec.map (CommRingCat.ofHom
    (nodalLowerReindexedOutput D d hdepth hm e hl a2 h2 a c).toRingHom)

/-- Reindexing preserves the exact original tangent sum. -/
@[reassoc] theorem nodalLowerReindexedLift_contraction :
    nodalLowerReindexedLift D d hdepth hm e hl a2 h2 a c ≫ toCurve e =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  subst l
  exact nodalLowerLift_contraction D d hdepth hm e a2 h2 a c

/-- Reindexing preserves the original coefficient map. -/
@[reassoc] theorem nodalLowerReindexedLift_structure :
    nodalLowerReindexedLift D d hdepth hm e hl a2 h2 a c ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

/-- Reindexing preserves the nodal fiber's inclusion in the actual derivative open. -/
theorem nodalLowerReindexedOutput_nodal_mem
    (hlo : 2 * k < m) (hhi : m < 3 * k) (ha2 : a2 ∈ IsLocalRing.maximalIdeal R)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) :
    p ∈ PrimeSpectrum.basicOpen
      ((nodalLowerReindexedOutput D d hdepth hm e hl a2 h2 a c)
        (verticalDerivative W (π ^ l) e.b3 e.b4 e.b6)) := by
  subst l
  exact nodalLowerOutput_nodal_mem D d hdepth hm e a2 h2 a c hlo hhi ha2 p hp

end FLT.Mazur.WeierstrassDividedDepth
