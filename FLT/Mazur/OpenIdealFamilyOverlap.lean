/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionIdealDegree

/-!
# Full family comparisons on a common ambient open

Two separated ambients containing the same open give equivalent supported
finite locally free ideal families. The comparison restricts the full ideal
to the common open and extends it to the other ambient. Identity and cocycle
laws follow from full ideal recovery, without choosing a basis or a family
comparison witness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.OpenIdealCover

set_option backward.isDefEq.respectTransparency false

variable {W X Y Z S : Scheme.{u}} (p : W ⟶ S) (d : ℕ)

/-- Full ideal families on a common open identify with supported families in its ambient. -/
def openIdealFamilyEquivOver (i : W ⟶ X) [IsOpenImmersion i]
    (q : X ⟶ S) [IsSeparated q] (hi : i ≫ q = p) :
    { J : W.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ p) d } ≃
      { J : X.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ q) d ∧
        Set.range J.subschemeι ⊆ Set.range i } :=
  (Equiv.subtypeEquivRight fun J ↦ by rw [hi]).trans (openIdealFamilyEquiv i q d)

/-- Compare the actual supported families of two separated ambients through their common open. -/
def supportedFamilyChange (i : W ⟶ X) [IsOpenImmersion i]
    (q : X ⟶ S) [IsSeparated q] (hi : i ≫ q = p)
    (j : W ⟶ Y) [IsOpenImmersion j] (r : Y ⟶ S) [IsSeparated r] (hj : j ≫ r = p) :
    { J : X.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ q) d ∧
      Set.range J.subschemeι ⊆ Set.range i } ≃
    { J : Y.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ r) d ∧
      Set.range J.subschemeι ⊆ Set.range j } :=
  (openIdealFamilyEquivOver p d i q hi).symm.trans (openIdealFamilyEquivOver p d j r hj)

/-- The overlap comparison restricts and extends the entire ideal sheaf. -/
theorem supportedFamilyChange_ideal (i : W ⟶ X) [IsOpenImmersion i]
    (q : X ⟶ S) [IsSeparated q] (hi : i ≫ q = p)
    (j : W ⟶ Y) [IsOpenImmersion j] (r : Y ⟶ S) [IsSeparated r] (hj : j ≫ r = p)
    (J : { J : X.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ q) d ∧
      Set.range J.subschemeι ⊆ Set.range i }) :
    (supportedFamilyChange p d i q hi j r hj J).val = (J.val.comap i).map j := rfl

/-- Comparing an ambient with itself fixes every full supported ideal family. -/
theorem supportedFamilyChange_self (i : W ⟶ X) [IsOpenImmersion i]
    (q : X ⟶ S) [IsSeparated q] (hi : i ≫ q = p)
    (J : { J : X.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ q) d ∧
      Set.range J.subschemeι ⊆ Set.range i }) :
    supportedFamilyChange p d i q hi i q hi J = J :=
  Equiv.apply_symm_apply (openIdealFamilyEquivOver p d i q hi) J

/-- Three containing ambients satisfy the cocycle on every actual full ideal family. -/
theorem supportedFamilyChange_cocycle (i : W ⟶ X) [IsOpenImmersion i]
    (q : X ⟶ S) [IsSeparated q] (hi : i ≫ q = p)
    (j : W ⟶ Y) [IsOpenImmersion j] (r : Y ⟶ S) [IsSeparated r] (hj : j ≫ r = p)
    (k : W ⟶ Z) [IsOpenImmersion k] (a : Z ⟶ S) [IsSeparated a] (hk : k ≫ a = p)
    (J : { J : X.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ q) d ∧
      Set.range J.subschemeι ⊆ Set.range i }) :
    supportedFamilyChange p d j r hj k a hk
        (supportedFamilyChange p d i q hi j r hj J) =
      supportedFamilyChange p d i q hi k a hk J := by
  exact congrArg (openIdealFamilyEquivOver p d k a hk)
    (Equiv.symm_apply_apply (openIdealFamilyEquivOver p d j r hj) _)

end FLT.Mazur.OpenIdealCover
