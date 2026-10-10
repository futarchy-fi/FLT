/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealAmbientHom
public import FLT.Mazur.OpenImmersionIdealDegree

/-!
# Full relative ideal extension through an original ambient open

An open embedding into a separated ambient extends every finite locally
free full ideal family, preserving its degree. The extended support remains
inside the original open and restriction recovers the entire ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {A B S X : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
variable (i : A ⟶ B) [IsOpenImmersion i] (hi : i ≫ b = a)
variable (s : X ⟶ S) (d : ℕ) [IsSeparated b]

/-- Extension through an original ambient chart preserves finite locally free degree. -/
theorem relativeIdealExtension_degree (J : RelativeIdealFamilies a d s) :
    FiniteLocallyFreeDegree
      ((J.val.map (relativeIdealAmbientHom a b i hi s)).subschemeι ≫ pullback.fst s b) d := by
  have h : FiniteLocallyFreeDegree
      (J.val.subschemeι ≫ relativeIdealAmbientHom a b i hi s ≫ pullback.fst s b) d := by
    rw [relativeIdealAmbientHom_fst]
    exact J.property
  exact (openIdealFamilyEquiv (relativeIdealAmbientHom a b i hi s)
    (pullback.fst s b) d ⟨J.val, h⟩).property.1

/-- The actual extended family in the base change of the containing separated ambient. -/
def relativeIdealFamilyExtension (J : RelativeIdealFamilies a d s) :
    RelativeIdealFamilies b d s :=
  ⟨J.val.map (relativeIdealAmbientHom a b i hi s),
    relativeIdealExtension_degree a b i hi s d J⟩

/-- The extended full family is supported in the base change of its original ambient open. -/
theorem relativeIdealFamilyExtension_support (J : RelativeIdealFamilies a d s) :
    Set.range (relativeIdealFamilyExtension a b i hi s d J).val.subschemeι ⊆
      Set.range (relativeIdealAmbientHom a b i hi s) := by
  have h : FiniteLocallyFreeDegree
      (J.val.subschemeι ≫ relativeIdealAmbientHom a b i hi s ≫ pullback.fst s b) d := by
    rw [relativeIdealAmbientHom_fst]
    exact J.property
  exact (openIdealFamilyEquiv (relativeIdealAmbientHom a b i hi s)
    (pullback.fst s b) d ⟨J.val, h⟩).property.2

/-- Restriction recovers the entire original ideal after extending to the containing ambient. -/
theorem relativeIdealFamilyExtension_restrict (J : RelativeIdealFamilies a d s) :
    (relativeIdealFamilyExtension a b i hi s d J).val.comap
      (relativeIdealAmbientHom a b i hi s) = J.val := by
  have h : FiniteLocallyFreeDegree
      (J.val.subschemeι ≫ relativeIdealAmbientHom a b i hi s ≫ pullback.fst s b) d := by
    rw [relativeIdealAmbientHom_fst]
    exact J.property
  let e := openIdealFamilyEquiv (relativeIdealAmbientHom a b i hi s) (pullback.fst s b) d
  exact congrArg Subtype.val (e.left_inv ⟨J.val, h⟩)

end FLT.Mazur.ClosedIdealCover
