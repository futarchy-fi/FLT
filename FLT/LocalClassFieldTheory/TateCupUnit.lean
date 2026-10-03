/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateCupComparison
public import FLT.LocalClassFieldTheory.TateTwoClassOperation

/-!
# Normalization of the Tate cup on the scalar unit

The degree-zero Tate class of `1` cups to the supplied two-class, compared
through the actual positive Tate isomorphism. This fixes the sign.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (k G : Type) [CommRing k] [Group G] [Fintype G]

omit [Fintype G] in
/-- The scalar zero-cochain `1` is closed. -/
theorem scalarOne_cycle :
    inhomogeneousCochains.d (Rep.trivial k G k) 0 (fun _ => (1 : k)) = 0 := by
  funext v
  change inhomogeneousCochains.d (Rep.trivial k G k) 0 (fun _ => (1 : k)) v = (0 : k)
  simp [inhomogeneousCochains.d_hom_apply]

/-- The actual degree-zero Tate class of the scalar unit. -/
def tateScalarUnit : tateCohomology (Rep.trivial k G k) 0 :=
  tateClassOfCochain _ 0 (fun _ => (1 : k)) (scalarOne_cycle k G)

variable {k G} (M : Rep k G) (c : cocycles₂ M)

omit [Fintype G] in
/-- The ordinary cup with the scalar unit represents the original two-cocycle. -/
theorem scalarCupTwo_one_class :
    π M 2 (cocyclesMk (scalarCupTwo M c (n := 0) (fun _ => (1 : k)))
      (scalarCupTwo_cycle M c _ (scalarOne_cycle k G))) = H2π M c := by
  change π M 2 _ = π M 2 ((isoCocycles₂ M).inv c)
  congr 1
  rw [← cocyclesMk₂_eq M c]
  apply (ModuleCat.mono_iff_injective (iCocycles M 2)).mp inferInstance
  calc
    _ = scalarCupTwo M c (n := 0) (fun _ => (1 : k)) := iCocycles_mk _ _
    _ = (cochainsIso₂ M).inv c := by
      funext v
      exact one_smul k (c (v 0, v 1))
    _ = _ := (iCocycles_mk _ _).symm

/-- The all-degree construction has the expected positive normalization at the Tate unit. -/
theorem tateTwoExtensionMap_unit :
    ((TateCohomology.isoGroupCohomology 2).app M).hom
      (tateTwoExtensionMap M c 0 (tateScalarUnit k G)) = H2π M c :=
  (tateTwoExtensionMap_positive_cup M c (n := 0) _ (scalarOne_cycle k G)).trans
    (scalarCupTwo_one_class M c)

/-- Cup with an actual two-class sends the Tate unit to that class. -/
theorem tateTwoClassMap_unit (a : groupCohomology M 2) :
    ((TateCohomology.isoGroupCohomology 2).app M).hom
      (tateTwoClassMap M a 0 (tateScalarUnit k G)) = a :=
  (tateTwoExtensionMap_unit M (twoClassRepresentative M a)).trans
    (twoClassRepresentative_spec M a)

/-- Equivalently, cup with the scalar unit gives the corresponding actual Tate two-class. -/
theorem tateTwoClassMap_unit_eq (a : groupCohomology M 2) :
    tateTwoClassMap M a 0 (tateScalarUnit k G) =
      ((TateCohomology.isoGroupCohomology 2).app M).inv a := by
  apply (ModuleCat.mono_iff_injective
    ((TateCohomology.isoGroupCohomology 2).app M).hom).mp inferInstance
  rw [tateTwoClassMap_unit]
  exact (Iso.inv_hom_id_apply _ _).symm

end LocalClassFieldTheory
