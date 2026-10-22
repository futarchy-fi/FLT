/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorTrivialRelation
public import FLT.Mazur.FilteredFlatRelationFamily

/-!
# Eventual vanishing of the whole fixed ideal-tensor obstruction

A flat colimit kills the entire obstruction at a Noetherian algebra stage
after one transition. The finite family is derived from the kernel, not
supplied as extra data. This proves zero of the old obstruction map; it
does not assert that the new stage is flat or has zero obstruction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.Approximation
open IdealTensorKernel RingFlatRelation
universe u v w
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F G : I ⥤ CommRingCat.{u}) (c : Cocone F) (d : Cocone G)
  (hc : IsColimit c) (hd : IsColimit d)
  [PreservesColimit F (forget CommRingCat)]
  [PreservesColimit G (forget CommRingCat)]
  (η : F ⟶ G) (φ : c.pt →+* d.pt)
  (hφ : ∀ i, (d.ι.app i).hom.comp (η.app i).hom = φ.comp (c.ι.app i).hom)

include hc hd hφ in
/-- Every element of the original kernel dies at one stage and at every later stage. -/
theorem exists_obstruction_vanishing_stage (hflat : φ.Flat)
    (i : I) [IsNoetherianRing (G.obj i)] (J : Ideal (F.obj i)) (hJ : J.FG) :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k),
      let _ := (η.app i).hom.toAlgebra
      let _ := (η.app k).hom.toAlgebra
      ∀ z : obstruction (S := G.obj i) J,
        transition (F.map (g ≫ e)).hom (G.map (g ≫ e)).hom
          (congrArg CommRingCat.Hom.hom (η.naturality (g ≫ e)).symm) J z.val = 0 := by
  classical
  let _ := (η.app i).hom.toAlgebra
  obtain ⟨n, z, hz⟩ := exists_generators (S := G.obj i) J hJ
  have hm (t : Fin n) : z t ∈ obstruction (S := G.obj i) J := by
    rw [← hz]
    exact Submodule.subset_span (Set.mem_range_self t)
  choose m x a ha hx using fun t ↦ exists_relation J ⟨z t, hm t⟩
  change ∀ t, (∑ l, x t l ⊗ₜ[F.obj i] a t l) = z t at ha
  have hrel (t : Fin n) :
      let a' : Fin (m t) → c.pt := fun l ↦ c.ι.app i ((a t l).val)
      let x' : Fin (m t) → d.pt := fun l ↦ d.ι.app i (x t l)
      ∑ l, φ (a' l) * x' l = 0 := by
    have hx' : ∑ l, x t l * η.app i ((a t l).val) = 0 := hx t
    have h := congrArg (d.ι.app i) hx'
    have hcomm (b : F.obj i) : d.ι.app i (η.app i b) = φ (c.ι.app i b) :=
      RingHom.congr_fun (hφ i) b
    simpa only [map_sum, map_mul, map_zero, hcomm, mul_comm] using h
  obtain ⟨j, g, hg⟩ := exists_flat_relation_family_stage F G c d hc hd η φ hφ hflat
    (fun t ↦ Fin (m t)) i (fun t l ↦ (a t l).val) x hrel
  refine ⟨j, g, fun k e ↦ ?_⟩
  let _ := (η.app k).hom.toAlgebra
  let q := transition (F.map (g ≫ e)).hom (G.map (g ≫ e)).hom
    (congrArg CommRingCat.Hom.hom (η.naturality (g ≫ e)).symm) J
  have hq (t : Fin n) : q (z t) = 0 := by
    have ht := trivial_map (η.app j).hom (η.app k).hom
      (F.map e).hom (G.map e).hom
      (congrArg CommRingCat.Hom.hom (η.naturality e).symm) _ _ (hg t)
    have ht' : Trivial (η.app k).hom
        (fun l ↦ F.map (g ≫ e) ((a t l).val))
        (fun l ↦ G.map (g ≫ e) (x t l)) := by
      simpa only [F.map_comp, G.map_comp, CommRingCat.comp_apply] using ht
    rw [← ha t, map_sum]
    exact sum_tmul_eq_zero_of_trivial (J.map (F.map (g ≫ e)).hom)
      (fun l ↦ idealTransition (F.map (g ≫ e)).hom J (a t l))
      (fun l ↦ G.map (g ≫ e) (x t l)) ht'
  have hk : obstruction (S := G.obj i) J ≤ LinearMap.ker q := by
    rw [← hz]
    exact Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hq t)
  change ∀ z : obstruction (S := G.obj i) J, q z.val = 0
  intro z
  exact hk z.property

end FLT.Mazur.Approximation
