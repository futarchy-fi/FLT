/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeNormalizedParameters
public import FLT.Mazur.EllipticSplitDepthResidueCharacter

/-!
# A single original parameter on every component

Choose the positive lift of each component label. Negative branches acquire
one copy of the original period coefficient; midpoint points use the positive
tangent. On the original smooth locus use its actual reduction character.
Primitive-witness independence is proved from the original point coordinates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} {P : (W.map (algebraMap A K)).toProjective.Point}

/-- The parameter using the nonnegative representative of the component label. -/
def nodeCoordinateParameter (n : ℕ) (c₆ : A) (v : NodePointCoordinates A W π P) :
    ResidueField A := by
  classical
  exact if 2 * v.depth = n ∨ v.b ∈ maximalIdeal A then nodePositiveParameter v
    else nodeWrapParameter W c₆ * nodeNegativeParameter v

variable (D : SplitNodeDepth W π n) (c₆ : A)

/-- A parameter of the original generic point, with no choice of replacement specialization. -/
def nodePointParameter (P : (W.map (algebraMap A K)).toProjective.Point) : ResidueField A := by
  classical
  exact if h : SmoothReduction A W P then
    (Additive.toMul (splitDepthSmoothCharacter D ⟨P, h⟩)).val
  else nodeCoordinateParameter n c₆
    (exists_nodePointCoordinates A W π D.maximalIdeal_eq n
      D.a₃_mem D.a₄_mem D.a₆_not_mem P h).choose

/-- On the original smooth component this is precisely the original smooth character. -/
theorem nodePointParameter_smooth [dec : DecidableEq (ResidueField A)]
    (P : ellipticE0 A W) :
    nodePointParameter D c₆ P.val = (Additive.toMul (splitDepthSmoothCharacter D P)).val := by
  have hc : dec = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  cases hc
  have hp : SmoothReduction A W P.val := P.property
  rw [nodePointParameter, dite_eq_left hp]

/-- Any original coordinate witness computes the same nonidentity parameter. -/
theorem nodePointParameter_of_coordinates (v : NodePointCoordinates A W π P)
    (hp : ¬ SmoothReduction A W P) :
    nodePointParameter D c₆ P = nodeCoordinateParameter n c₆ v := by
  classical
  rw [nodePointParameter, dite_eq_right hp]
  obtain ⟨hd, ha, hb⟩ :=
    ((exists_nodePointCoordinates A W π D.maximalIdeal_eq n
      D.a₃_mem D.a₄_mem D.a₆_not_mem P hp).choose).unique
      D.uniformizer_ne_zero D.maximalIdeal_eq v
  simp only [nodeCoordinateParameter, nodePositiveParameter, nodeNegativeParameter, hd, ha, hb]

/-- A primitive parameter is unchanged by equality of its depth and both divided residues. -/
theorem nodeCoordinateParameter_eq_of_residues
    {Q : (W.map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hd : v.depth = w.depth) (ha : residue A v.a = residue A w.a)
    (hb : residue A v.b = residue A w.b) :
    nodeCoordinateParameter n c₆ v = nodeCoordinateParameter n c₆ w := by
  classical
  simp only [nodeCoordinateParameter, nodePositiveParameter, nodeNegativeParameter,
    ← residue_eq_zero_iff, map_add, map_mul, hd, ha, hb]

end FLT.Mazur
