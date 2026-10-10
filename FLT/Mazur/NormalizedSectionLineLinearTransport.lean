/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineSheaf

/-!
# Actual line submodules under changes of ambient coordinates

An ambient linear equivalence maps the line to its genuine image submodule.
Whenever a coordinate of its transported generator is a unit, this image
has that coordinate as a trivialization. Tilde gives an isomorphism of the
actual line sheaves, commuting with the original ambient linear map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
variable {R : Type u} [CommRing R] {ι κ : Type u}

/-- The image line has invertible projection whenever the transported generator does. -/
def linearTransport (e : (ι → R) ≃ₗ[R] (κ → R)) (i : ι) (j : κ)
    (L : Chart R ι i) (a : Rˣ) (ha : e (generator R ι i L) j = a) : Chart R κ j := by
  refine ⟨L.val.map e.toLinearMap, ?_⟩
  let d := e.submoduleMap L.val
  let t := d.symm.trans ((trivialization R ι i L).trans
    (LinearEquiv.smulOfUnit a : R ≃ₗ[R] R))
  have ht : (coordinate R κ j (L.val.map e.toLinearMap) : _ → R) = t := by
    funext v
    obtain ⟨w, rfl⟩ := d.surjective v
    have h := congrArg (fun x ↦ e x j) (eq_smul_generator R ι i L w)
    dsimp only [t, LinearEquiv.trans_apply]
    rw [d.symm_apply_apply]
    change e w.val j = (a : R) * w.val i
    rw [e.map_smul] at h
    simpa only [Pi.smul_apply, smul_eq_mul, ha, mul_comm] using h
  rw [ht]
  exact t.bijective

/-- The constructed chart is the image of the original submodule under the original linear map. -/
lemma linearTransport_val (e : (ι → R) ≃ₗ[R] (κ → R)) (i : ι) (j : κ)
    (L : Chart R ι i) (a : Rˣ) (ha : e (generator R ι i L) j = a) :
    (linearTransport e i j L a ha).val = L.val.map e.toLinearMap := rfl

/-- The transported normalized generator is the original image divided by its unit coordinate. -/
lemma generator_linearTransport (e : (ι → R) ≃ₗ[R] (κ → R)) (i : ι) (j : κ)
    (L : Chart R ι i) (a : Rˣ) (ha : e (generator R ι i L) j = a) :
    generator R κ j (linearTransport e i j L a ha) =
      (↑a⁻¹ : R) • e (generator R ι i L) := by
  have hm : e (generator R ι i L) ∈ (linearTransport e i j L a ha).val :=
    ⟨generator R ι i L, generator_mem R ι i L, rfl⟩
  have h := eq_smul_generator R κ j (linearTransport e i j L a ha)
    ⟨e (generator R ι i L), hm⟩
  change e (generator R ι i L) =
    e (generator R ι i L) j • generator R κ j (linearTransport e i j L a ha) at h
  rw [ha] at h
  rw [h, smul_smul, Units.inv_mul, one_smul]

/-- Transport of the actual line sheaf by the original ambient coefficient isomorphism. -/
def sheafLinearTransport (e : (ι → R) ≃ₗ[R] (κ → R)) (i : ι) (j : κ)
    (L : Chart R ι i) (a : Rˣ) (ha : e (generator R ι i L) j = a) :
    sheaf i L ≅ sheaf j (linearTransport e i j L a ha) :=
  (tilde.functor (.of R)).mapIso (e.submoduleMap L.val).toModuleIso

/-- The sheaf transport commutes with the actual ambient coordinate transformation. -/
lemma sheafLinearTransport_inclusion (e : (ι → R) ≃ₗ[R] (κ → R)) (i : ι) (j : κ)
    (L : Chart R ι i) (a : Rˣ) (ha : e (generator R ι i L) j = a) :
    (sheafLinearTransport e i j L a ha).hom ≫
        sheafInclusion j (linearTransport e i j L a ha) =
      sheafInclusion i L ≫ (tilde.functor (.of R)).map (ModuleCat.ofHom e.toLinearMap) := by
  change (tilde.functor (.of R)).map _ ≫ (tilde.functor (.of R)).map _ =
    (tilde.functor (.of R)).map _ ≫ (tilde.functor (.of R)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end FLT.Mazur.NormalizedSectionLine
