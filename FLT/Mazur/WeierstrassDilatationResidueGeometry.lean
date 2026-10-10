/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueFiber
public import FLT.Mazur.NodalFiberNodeComparison
public import FLT.Mazur.NodalFiberUnitComparison
public import FLT.Mazur.PolygonNodeBranches

/-!
# Residue geometry of the actual integral divided charts

Before the middle depth the actual tensor fiber is the existing split node,
with its two open smooth Laurent branches. At the middle depth it is itself
a Laurent chart. All comparisons are over the original residue field.
-/

@[expose] public noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

/-- An algebra equivalence induces a spectrum isomorphism over its coefficient ring. -/
theorem algebraSpecIso_structure {K A B : Type u}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) :
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  have h : CommRingCat.ofHom (algebraMap K A) ≫ CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom (algebraMap K B) := by
    ext r
    exact e.commutes r
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (algebraMap K A) ≫
    CommRingCat.ofHom e.toRingHom) = _
  rw [h]

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

/-- The actual tensor residue fiber is the existing oriented polygon node below middle depth. -/
def residuePolygonEquiv (hstrict : 2 * k < n) :
    ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R) ≃ₐ[ResidueField R]
      PolygonNodeEqualizer.A (R := ResidueField R) :=
  (residueNodeEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).trans
    NodalFiber.polygonNodeEquiv

/-- The actual tensor residue fiber is a Laurent algebra at exact middle depth. -/
def residueLaurentEquiv (hmiddle : 2 * k = n) :
    ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R) ≃ₐ[ResidueField R]
      (ResidueField R)[T;T⁻¹] := by
  have hc := (divided_constant_isUnit D k hmiddle b6 h6).map (residue R)
  have e := NodalFiber.laurentEquiv hc.unit
  rw [hc.unit_spec] at e
  exact (residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).trans e

/-- The original tensor fiber has its actual structure map to the residue spectrum. -/
def residueStructure :
    Spec (.of (ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R))) ⟶
      Spec (.of (ResidueField R)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ResidueField R) (ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R))))

variable (hstrict : 2 * k < n)

/-- The node comparison is an actual isomorphism of schemes. -/
def residueNodeIso : PolygonNodeBranches.node (ResidueField R) ≅
    Spec (.of (ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R))) :=
  Scheme.Spec.mapIso
    (residuePolygonEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).toRingEquiv.toCommRingCatIso.op

/-- The actual node isomorphism respects the residue-field structure. -/
@[reassoc] theorem residueNodeIso_structure :
    (residueNodeIso D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).hom ≫
        residueStructure k b3 b4 b6 = PolygonNodeBranches.toBase (ResidueField R) :=
  algebraSpecIso_structure _

/-- The first punctured branch maps into the actual tensor residue fiber. -/
def residueLeftBranch : Spec (.of ((ResidueField R)[T;T⁻¹])) ⟶
    Spec (.of (ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R))) :=
  PolygonNodeBranches.left (ResidueField R) ≫
    (residueNodeIso D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).hom

/-- The second punctured branch maps into that same tensor residue fiber. -/
def residueRightBranch : Spec (.of ((ResidueField R)[T;T⁻¹])) ⟶
    Spec (.of (ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R))) :=
  PolygonNodeBranches.right (ResidueField R) ≫
    (residueNodeIso D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).hom

instance residueLeftBranch_isOpenImmersion :
    IsOpenImmersion (residueLeftBranch D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance residueRightBranch_isOpenImmersion :
    IsOpenImmersion (residueRightBranch D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The first branch retains the actual multiplicative-group structure morphism. -/
theorem residueLeftBranch_structure :
    residueLeftBranch D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
        residueStructure k b3 b4 b6 = (MultiplicativeGroupScheme.gm (ResidueField R)).hom := by
  rw [residueLeftBranch, Category.assoc, residueNodeIso_structure,
    PolygonNodeBranches.left_toBase]

/-- The second branch has the same smooth Laurent structure. -/
theorem residueRightBranch_structure :
    residueRightBranch D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
        residueStructure k b3 b4 b6 = (MultiplicativeGroupScheme.gm (ResidueField R)).hom := by
  rw [residueRightBranch, Category.assoc, residueNodeIso_structure,
    PolygonNodeBranches.right_toBase]

instance residueLeftBranch_smooth :
    Smooth (residueLeftBranch D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
      residueStructure k b3 b4 b6) := by
  rw [residueLeftBranch_structure]
  exact MultiplicativeGroupScheme.smooth _

instance residueRightBranch_smooth :
    Smooth (residueRightBranch D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
      residueStructure k b3 b4 b6) := by
  rw [residueRightBranch_structure]
  exact MultiplicativeGroupScheme.smooth _

end FLT.Mazur.WeierstrassDilatation
