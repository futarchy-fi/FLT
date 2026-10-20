/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFamilyComparison
public import FLT.Mazur.WeierstrassDividedResolvedProductOpens

/-!
# The resolved smooth product across coefficient family lengths

Transport both whole smooth loci and their relative product by the proved
comparison of global finite models. The two actual input projections retain
their coefficient structures.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n m : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (other : (i : Fin (m + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (hm : j ≤ m)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "base'" => finiteGlobalStructure hπ other j hm
local notation "U" => (base).smoothLocus
local notation "V" => (base').smoothLocus
local notation "t" => (U).ι ≫ base
local notation "t'" => (V).ι ≫ base'

/-- The whole smooth loci agree under the actual global model comparison. -/
theorem finiteSmoothLocus_family_heq : HEq U V := by
  congr! 1
  · exact finiteGlobalModel_family_eq hπ data other j hj hm
  · exact finiteGlobalStructure_family_heq hπ data other j hj hm

/-- The smooth schemes themselves are independent of unused family entries. -/
theorem finiteSmoothScheme_family_eq : (U).toScheme = (V).toScheme := by
  congr! 1
  · exact finiteGlobalModel_family_eq hπ data other j hj hm
  · exact finiteSmoothLocus_family_heq hπ data other j hj hm

/-- The smooth open immersions preserve their actual global inclusions. -/
theorem finiteSmoothInclusion_family_heq : HEq (U).ι (V).ι := by
  congr! 1
  · exact finiteGlobalModel_family_eq hπ data other j hj hm
  · exact finiteSmoothLocus_family_heq hπ data other j hj hm

/-- The relative smooth coefficient maps agree. -/
theorem finiteSmoothStructure_family_heq : HEq t t' := by
  exact heq_comp (finiteSmoothScheme_family_eq hπ data other j hj hm)
    (finiteGlobalModel_family_eq hπ data other j hj hm) rfl
    (finiteSmoothInclusion_family_heq hπ data other j hj hm)
    (finiteGlobalStructure_family_heq hπ data other j hj hm)

/-- The explicit smooth identification preserves the coefficient map. -/
@[reassoc] theorem finiteSmoothScheme_family_structure :
    eqToHom (finiteSmoothScheme_family_eq hπ data other j hj hm) ≫ t' = t := by
  apply eq_of_heq
  exact (eqToHom_comp_heq _ _).trans
    (finiteSmoothStructure_family_heq hπ data other j hj hm).symm


/-- The complete relative product is unchanged by the total family length. -/
theorem finiteResolvedProduct_family_eq :
    finiteResolvedProduct hπ data j hj = finiteResolvedProduct hπ other j hm := by
  unfold finiteResolvedProduct
  congr! 1
  · exact finiteSmoothScheme_family_eq hπ data other j hj hm
  · exact finiteSmoothScheme_family_eq hπ data other j hj hm
  · exact finiteSmoothStructure_family_heq hπ data other j hj hm
  · exact finiteSmoothStructure_family_heq hπ data other j hj hm

/-- The first projection is transported along with the whole product. -/
theorem finiteResolvedFst_family_heq :
    HEq (pullback.fst t t) (pullback.fst t' t') := by
  congr! 1
  · exact finiteSmoothScheme_family_eq hπ data other j hj hm
  · exact finiteSmoothScheme_family_eq hπ data other j hj hm
  · exact finiteSmoothStructure_family_heq hπ data other j hj hm
  · exact finiteSmoothStructure_family_heq hπ data other j hj hm

/-- The second projection is transported along with the whole product. -/
theorem finiteResolvedSnd_family_heq :
    HEq (pullback.snd t t) (pullback.snd t' t') := by
  congr! 1
  · exact finiteSmoothScheme_family_eq hπ data other j hj hm
  · exact finiteSmoothScheme_family_eq hπ data other j hj hm
  · exact finiteSmoothStructure_family_heq hπ data other j hj hm
  · exact finiteSmoothStructure_family_heq hπ data other j hj hm

/-- The first input's coefficient point is retained by the explicit product comparison. -/
@[reassoc] theorem finiteResolvedProduct_family_structure :
    eqToHom (finiteResolvedProduct_family_eq hπ data other j hj hm) ≫
      pullback.fst t' t' ≫ t' = pullback.fst t t ≫ t := by
  apply eq_of_heq
  apply (eqToHom_comp_heq _ _).trans
  exact (heq_comp (finiteResolvedProduct_family_eq hπ data other j hj hm)
    (finiteSmoothScheme_family_eq hπ data other j hj hm) rfl
    (finiteResolvedFst_family_heq hπ data other j hj hm)
    (finiteSmoothStructure_family_heq hπ data other j hj hm)).symm

end FLT.Mazur.WeierstrassDividedDepth
