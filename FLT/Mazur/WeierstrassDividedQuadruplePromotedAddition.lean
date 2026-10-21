/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalQuadrupleAdditionSourceCoverage
public import FLT.Mazur.WeierstrassDividedSmoothFamilyComparison
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Promote exact quadruple-depth outputs into an arbitrary supplied family

The canonical doubled family and the supplied family give the same finite
smooth model at the doubled depth. Transport the entire constructed output
through that proved equality, then promote it to the chosen final stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k : ℕ}
  (D : SplitNodeDepth W π (4 * k))
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hkk : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "old" => splitNodeDoubledFamily D
local notation "base" => finiteGlobalStructure hπ old (k + k) le_rfl
local notation "U" => (base).smoothLocus
local notation "base'" => finiteGlobalStructure hπ data (k + k) hkk
local notation "V" => (base').smoothLocus
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "eqS" => finiteSmoothScheme_family_eq hπ old data (k + k) le_rfl hkk

/-- The smooth family identification retains the whole original cubic contraction. -/
@[reassoc] theorem quadrupleFamilyTransport_contraction :
    eqToHom eqS ≫ (V).ι ≫ finiteGlobalContraction hπ data (k + k) hkk =
      (U).ι ≫ finiteGlobalContraction hπ old (k + k) le_rfl := by
  apply eq_of_heq
  apply (eqToHom_comp_heq _ _).trans
  exact (heq_comp eqS
    (finiteGlobalModel_family_eq hπ old data (k + k) le_rfl hkk) rfl
    (finiteSmoothInclusion_family_heq hπ old data (k + k) le_rfl hkk)
    (finiteGlobalContraction_family_heq hπ old data (k + k) le_rfl hkk)).symm

variable (j : ℕ) (hj : j ≤ n) (hstage : k + k ≤ j)
local notation "final" => finiteGlobalStructure hπ data j hj
local notation "Uf" => (final).smoothLocus

/-- The exact quadruple-depth output in the unchanged supplied final smooth model. -/
def quadruplePromotedAddition : (O).toScheme ⟶ (Uf).toScheme :=
  nodalQuadrupleAddition D d a c ≫ eqToHom eqS ≫
    finiteGlobalSmoothTransition hπ data (k + k) j hstage hj

/-- Promotion leaves the original cubic-valued output unchanged on its whole domain. -/
@[reassoc] theorem quadruplePromotedAddition_contraction :
    quadruplePromotedAddition D data hkk d a c j hj hstage ≫ (Uf).ι ≫
        finiteGlobalContraction hπ data j hj =
      nodalQuadrupleAddition D d a c ≫ (U).ι ≫
        finiteGlobalContraction hπ old (k + k) le_rfl := by
  rw [quadruplePromotedAddition, Category.assoc, Category.assoc,
    finiteGlobalSmoothTransition_contraction, quadrupleFamilyTransport_contraction]

/-- The output retains the actual original coefficient point after both transports. -/
@[reassoc] theorem quadruplePromotedAddition_structure :
    quadruplePromotedAddition D data hkk d a c j hj hstage ≫ (Uf).ι ≫ final =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [quadruplePromotedAddition, Category.assoc, Category.assoc,
    finiteGlobalSmoothTransition_structure, finiteSmoothScheme_family_structure,
    nodalQuadrupleAddition_structure]

end FLT.Mazur.WeierstrassDividedDepth
