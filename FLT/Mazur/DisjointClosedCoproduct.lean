/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Disjoint closed subschemes and products of ideals

A finite disjoint union of closed subschemes is the closed subscheme defined
by the product of their ideals. The comparison preserves the actual inclusion
in the ambient scheme, not just its underlying support.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.DisjointClosedCoproduct
variable {ι : Type} [Finite ι] {X : ι → Scheme.{u}} {Y : Scheme.{u}}
  (s : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (s i)]
  (hd : Pairwise fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j)))

include hd
/-- A finite disjoint coproduct of closed immersions is a closed immersion. -/
theorem closed : IsClosedImmersion (Sigma.desc s) := by
  have : SurjectiveOnStalks (Sigma.desc s) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) fun _ ↦ inferInstance
  refine ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (Sigma.desc s).continuous ?_ ?_⟩
  · intro x y he
    obtain ⟨i, x, rfl⟩ := (sigmaOpenCover X).exists_eq x
    obtain ⟨j, y, rfl⟩ := (sigmaOpenCover X).exists_eq y
    have he' : s i x = s j y := by simpa [← Scheme.Hom.comp_apply] using he
    obtain rfl : i = j := by
      by_contra hij
      exact Set.disjoint_left.mp (hd hij) ⟨x, rfl⟩ ⟨y, he'.symm⟩
    exact congrArg (Sigma.ι X i) ((s i).isClosedEmbedding.injective he')
  · intro Z hZ
    have he : Sigma.desc s '' Z = ⋃ i, s i '' (Sigma.ι X i ⁻¹' Z) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, x, rfl⟩ := (sigmaOpenCover X).exists_eq x
        exact Set.mem_iUnion.mpr ⟨i, x, hx, by simp [← Scheme.Hom.comp_apply]⟩
      · intro hy
        obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
        exact ⟨Sigma.ι X i x, hx, by simp [← Scheme.Hom.comp_apply]⟩
    rw [he]
    exact isClosed_iUnion_of_finite fun i ↦ (s i).isClosedEmbedding.isClosedMap _
      (hZ.preimage (Sigma.ι X i).continuous)

/-- The union has the intersection of the component kernels. -/
theorem kernel : (Sigma.desc s).ker = ⨅ i, (s i).ker := by
  let := closed s hd
  simpa using ((Sigma.desc s).iInf_ker_openCover_map_comp (sigmaOpenCover X)).symm

variable [Fintype ι]

/-- Disjoint closed supports make the product equal to the union kernel. -/
theorem product_eq_kernel : (∏ i, (s i).ker) = (Sigma.desc s).ker := by
  classical
  rw [kernel s hd]
  ext U
  simp only [Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  have hp : (∏ i, (s i).ker).ideal U = ∏ i, (s i).ker.ideal U := by
    exact map_prod (show Y.IdealSheafData →* Ideal Γ(Y, U) from
      { toFun := fun I ↦ I.ideal U
        map_one' := by simp
        map_mul' := fun _ _ ↦ rfl }) _ _
  rw [hp]
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp
  · intro i _ j _ hij
    apply Ideal.isCoprime_iff_sup_eq.mpr
    have he : (s i).ker ⊔ (s j).ker = ⊤ := by
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      rw [Scheme.IdealSheafData.support_sup]
      apply SetLike.coe_injective
      change ((s i).ker.support : Set Y) ∩ (s j).ker.support = ∅
      apply Set.disjoint_iff_inter_eq_empty.mp
      simpa [Scheme.Hom.support_ker, (s i).isClosedEmbedding.isClosed_range.closure_eq,
        (s j).isClosedEmbedding.isClosed_range.closure_eq] using hd hij
    exact congrArg (fun I : Y.IdealSheafData ↦ I.ideal U) he

/-- The disjoint union is the actual subscheme cut out by the ideal product. -/
def iso : (∐ X) ≅ (∏ i, (s i).ker).subscheme := by
  let := closed s hd
  have he : (∏ i, (s i).ker).subschemeι.ker = (Sigma.desc s).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, product_eq_kernel s hd]
  let f := IsClosedImmersion.lift (∏ i, (s i).ker).subschemeι (Sigma.desc s) he.le
  have : IsIso f := IsClosedImmersion.isIso_lift _ _ he
  exact asIso f

/-- The comparison respects the closed immersion into the ambient scheme. -/
@[reassoc (attr := simp)]
theorem iso_hom_ι : (iso s hd).hom ≫ (∏ i, (s i).ker).subschemeι = Sigma.desc s :=
  IsClosedImmersion.lift_fac _ _ _

/-- Every component retains its specified map into the ambient scheme. -/
@[reassoc]
theorem component_iso_hom_ι (i : ι) :
    Sigma.ι X i ≫ (iso s hd).hom ≫ (∏ i, (s i).ker).subschemeι = s i := by
  rw [iso_hom_ι, Sigma.ι_comp_desc]
end FLT.Mazur.DisjointClosedCoproduct
