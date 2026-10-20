/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TorusRootsOfUnitySubgroup
public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Roots-of-unity subgroups retain compatible torus coordinates

A full generalized-curve isomorphism preserving specified torus coordinates
identifies the root subgroups by the identity on their original carriers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {R : Type} [CommRing R] {E F : GeneralizedEllipticCurve (Spec (.of R))}
  (e : MultiplicativeGroupScheme.gm R ≅ E.group) [IsMonHom e.hom]
  (f : MultiplicativeGroupScheme.gm R ≅ F.group) [IsMonHom f.hom]
  (c : E ≅ F) (he : e.hom ≫ c.hom.group = f.hom) (n : ℕ) [NeZero n]

/-- A coordinate-preserving full curve comparison keeps the original root carrier. -/
def torusRootsOfUnityCompatibleIso : FiniteSubgroup.CompatibleIso
    (E.torusRootsOfUnitySubgroup e n) (F.torusRootsOfUnitySubgroup f n) where
  curve := c
  subgroup := Iso.refl _
  isMonHom := inferInstanceAs (IsMonHom (𝟙 (RootsOfUnityScheme.model R n)))
  compatible := by
    rw [Iso.refl_hom, Category.id_comp, torusRootsOfUnitySubgroup_curveMap,
      torusRootsOfUnitySubgroup_curveMap]
    simp only [Category.assoc]
    rw [c.hom.inclusion, ← Category.assoc e.hom, he]

/-- The compatible comparison is exactly the identity on the roots-of-unity scheme. -/
theorem torusRootsOfUnityCompatibleIso_subgroup :
    (torusRootsOfUnityCompatibleIso e f c he n).subgroup =
      Iso.refl (RootsOfUnityScheme.model R n) := rfl

end FLT.Mazur.GeneralizedEllipticCurve
