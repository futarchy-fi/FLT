/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudMaximalModel
public import FLT.GroupScheme.EtaleModelIdentification

/-!
# Generic maps out of the maximal model extend

The greatest coordinate image contains the pullback of every integral model.
This gives the prescribed integral map, without a ramification hypothesis.
In particular, every generic automorphism extends to the maximal model.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]

/-- A greatest coordinate image extends every generic map out of its model. -/
theorem extend_from_greatest_coordinate_image {X M : FF R K}
    (f : GenericGaloisHom X M) (hf : Function.Bijective f)
    (hmax : ∀ (Y : FF R K) (g : GenericGaloisHom X Y),
      g.integralCoordinateImage ≤ f.integralCoordinateImage)
    (Y : FF R K) (g : GenericGaloisHom M Y) :
    ∃! h : ModelHom M Y, genericHom h = g := by
  apply extend_generic_morphism_of_integral_coordinates M Y g
  intro y
  obtain ⟨m, hm⟩ := hmax Y (g.comp f)
    ((GenericGaloisHom.integralCoordinateMap (g.comp f)).mem_range_self y)
  refine ⟨m, (f.toBialgHom_injective hf.2) ?_⟩
  rw [← BialgHom.comp_apply, ← GenericGaloisHom.toBialgHom_comp]
  exact hm.symm

/-- Construct an actual model with the universal extension property, rather than
assuming one as model data. -/
theorem exists_maximal_model_extension (X : FF R K) :
    ∃ (M : FF R K) (f : GenericGaloisHom X M), Function.Bijective f ∧
      ∀ (Y : FF R K) (g : GenericGaloisHom M Y), ∃! h : ModelHom M Y, genericHom h = g := by
  obtain ⟨M, f, hf, hmax⟩ := exists_maximal_model X
  exact ⟨M, f, hf, extend_from_greatest_coordinate_image f hf hmax⟩

/-- A generic automorphism and its inverse extend to an integral automorphism. -/
theorem exists_maximal_model_automorphisms (X : FF R K) :
    ∃ (M : FF R K) (f : GenericGaloisHom X M), Function.Bijective f ∧
      ∀ g : GenericGaloisHom M M, Function.Bijective g →
        ∃ e : M.Iso M, genericHom e.toBialgHom = g := by
  obtain ⟨M, f, hf, hmax⟩ := exists_maximal_model_extension X
  refine ⟨M, f, hf, fun g hg ↦ ?_⟩
  obtain ⟨a, ha, -⟩ := hmax M g
  obtain ⟨b, hb, -⟩ := hmax M (g.inverse hg)
  have hab (x) : genericHom b (genericHom a x) = x := by
    rw [ha, hb, GenericGaloisHom.inverse_apply]
  have hba (x) : genericHom a (genericHom b x) = x := by
    obtain ⟨x, rfl⟩ := hg.2 x
    rw [ha, hb, GenericGaloisHom.inverse_apply]
  exact ⟨FF.isoOfGenericInverse a b hab hba, ha⟩

end ThreeAdicPlan
