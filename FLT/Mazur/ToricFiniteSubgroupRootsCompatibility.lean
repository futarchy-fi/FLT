/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ToricFiniteSubgroupRootsClassification
public import FLT.Mazur.GeneralizedCurveGeneratorTransport
public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Full-curve compatibility for classification of arbitrary toric subgroups

The classification is compatible with the entire generalized curve. In
particular it identifies full subgroup ideals, not merely their supports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ToricFiniteSubgroupRootsClassification

open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open ToricFiniteSubgroupHopfPresentation

variable {K : Type} [Field K] {E : GeneralizedEllipticCurve (Spec (.of K))}
  {n : ℕ} (H : E.FiniteSubgroup n)
  (e : MultiplicativeGroupScheme.gm K ≅ E.group) [IsMonHom e.hom]

include H e in
/-- A toric finite subgroup necessarily has positive scheme-theoretic degree. -/
theorem rank_pos : 0 < n := by
  rw [← coordinates_finrank H]
  exact LaurentHopfCyclicCharacters.finrank_pos (restriction H e) (restriction_surjective H e)

attribute [local irreducible] rootsIso

variable [NeZero n]

/-- The original subgroup and canonical roots are compatibly isomorphic on the full curve. -/
def compatibleIso : CompatibleIso H (E.torusRootsOfUnitySubgroup e n) where
  curve := Iso.refl E
  subgroup := rootsIso H e
  isMonHom := rootsIso_isMonHom H e
  compatible := by
    change H.curveMap ≫ 𝟙 _ = (rootsIso H e).hom ≫
      (RootsOfUnityScheme.inclusion K n ≫ e.hom) ≫ E.inclusion
    rw [Category.comp_id]
    exact (congrArg (fun g => g ≫ E.inclusion) (rootsIso_inclusion H e)).symm

/-- Classification leaves the full generalized curve itself unchanged. -/
theorem compatibleIso_curve : (compatibleIso H e).curve = Iso.refl E := rfl

attribute [local irreducible] compatibleIso

/-- Classification retains every multiplicity in the actual whole-curve defining ideal. -/
theorem ideal_eq_roots : H.ideal = (E.torusRootsOfUnitySubgroup e n).ideal := by
  have h := ideal_transport H (E.torusRootsOfUnitySubgroup e n)
    (compatibleIso H e).curve (compatibleIso H e).subgroup (compatibleIso H e).compatible
  rw [compatibleIso_curve] at h
  change _ = H.ideal.comap (𝟙 _) at h
  simpa only [Scheme.IdealSheafData.comap_id] using h.symm

end FLT.Mazur.ToricFiniteSubgroupRootsClassification
