/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticRootsOfUnitySections
public import FLT.Mazur.CyclotomicSchemeOrbit
public import FLT.Mazur.SupportedIdealOrbitComparison
public import FLT.Mazur.TorusRootsOfUnityCartier
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup

/-!
# Cyclotomic Cartier generators on full toric curves

A specialization of the integral cyclotomic root gives an actual subgroup
section whose powers cut out the whole subgroup divisor on the original curve.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve

open IntegralCyclotomicCoordinates ArithmeticRootsOfUnitySections

variable {R : Type} [CommRing R] (E : GeneralizedEllipticCurve (Spec (.of R)))
  (e : MultiplicativeGroupScheme.gm R ≅ E.group) [IsMonHom e.hom]
  (n : ℕ) [NeZero n] (φ : Coordinate n →+* R)

/-- The actual specialized cyclotomic unit has the required torsion relation. -/
theorem cyclotomicUnit_pow : (Units.map φ.toMonoidHom (rootUnit n)) ^ n = 1 := by
  apply Units.ext
  change φ (root n) ^ n = 1
  rw [← map_pow, root_pow, map_one]

/-- The specialized root as a section of the actual subgroup of the full curve. -/
def torusCyclotomicGenerator :
    𝟙_ (Over (Spec (.of R))) ⟶ (E.torusRootsOfUnitySubgroup e n).carrier :=
  rootSection R n (Units.map φ.toMonoidHom (rootUnit n)) (cyclotomicUnit_pow n φ)

/-- Its orbit in the curve is the actual Laurent unit orbit in the torus open. -/
theorem torusCyclotomicGenerator_orbit (k : ℕ) :
    (E.torusCyclotomicGenerator e n φ ^ k) ≫ (E.torusRootsOfUnitySubgroup e n).curveMap =
      ArithmeticTorusPoints.point R ((Units.map φ.toMonoidHom (rootUnit n)) ^ k) ≫
        e.hom ≫ E.inclusion := by
  rw [torusRootsOfUnitySubgroup_curveMap, ← Category.assoc]
  rw [← Category.assoc, torusCyclotomicGenerator, section_pow_inclusion, Category.assoc]

/-- The full subgroup ideal is the full cyclotomic orbit product on the curve. -/
theorem torusCyclotomicGenerator_ideal :
    (E.torusRootsOfUnitySubgroup e n).ideal = ∏ i : Fin n,
      ((E.torusCyclotomicGenerator e n φ ^ i.val) ≫
        (E.torusRootsOfUnitySubgroup e n).curveMap).left.ker := by
  let j := e.hom.left ≫ E.inclusion.left
  let i := fun k : Fin n ↦
    (ArithmeticTorusPoints.point R ((Units.map φ.toMonoidHom (rootUnit n)) ^ k.val)).left
  let _ : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let _ : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (e.hom.left ≫ E.inclusion.left))
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : ∀ k, IsClosedImmersion (i k ≫ j) := fun k ↦
    FCurve.isClosedImmersion_section E.curve.hom
      (ArithmeticTorusPoints.point R ((Units.map φ.toMonoidHom (rootUnit n)) ^ k.val) ≫
        e.hom ≫ E.inclusion).left
      (ArithmeticTorusPoints.point R ((Units.map φ.toMonoidHom (rootUnit n)) ^ k.val) ≫
        e.hom ≫ E.inclusion).w
  simp only [torusCyclotomicGenerator_orbit]
  change (E.torusRootsOfUnitySubgroup e n).ideal = ∏ k : Fin n, (i k ≫ j).ker
  refine OpenIdealCover.eq_ker_comp_prod j _ ?_ Finset.univ i ?_
  · rw [Scheme.IdealSheafData.range_subschemeι, FiniteSubgroup.ideal,
      Scheme.Hom.support_ker]
    rw [(E.torusRootsOfUnitySubgroup e n).curveMap.left.isClosedEmbedding.isClosed_range.closure_eq]
    rintro _ ⟨z, rfl⟩
    exact ⟨(RootsOfUnityScheme.inclusion R n).left z, rfl⟩
  · rw [torusRootsOfUnitySubgroup_ideal_on_torus, CyclotomicSchemeOrbit.ideal n φ]
    rfl

/-- The genuine arithmetic subgroup section is a Cartier generator on the whole curve. -/
theorem torusCyclotomicGenerator_cartier :
    (E.torusRootsOfUnitySubgroup e n).IsCartierGenerator
      (E.torusCyclotomicGenerator e n φ) :=
  ⟨section_pow_order R n _ _, E.torusRootsOfUnitySubgroup_relativeCartier e n,
    E.torusCyclotomicGenerator_ideal e n φ⟩

include φ in
/-- Cyclotomic specialization proves cyclicity of the actual toric subgroup. -/
theorem torusRootsOfUnitySubgroup_cyclotomic_isCyclic :
    (E.torusRootsOfUnitySubgroup e n).IsCyclic :=
  (E.torusCyclotomicGenerator_cartier e n φ).isCyclic _

end FLT.Mazur.GeneralizedEllipticCurve
