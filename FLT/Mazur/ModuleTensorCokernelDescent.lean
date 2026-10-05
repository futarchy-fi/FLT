/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineTensorExact
public import FLT.Mazur.ModuleSheafTensorAssociator
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Bilinear descent through sheaf cokernels

The tensor/internal-Hom adjunction supplies right exactness for arbitrary
module sheaves. Descending in both variables needs no flatness hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve
open ModuleSheafTensor ModuleSheafTensorCurrying ModuleSheafTensorAssociator

universe u

namespace FLT.Mazur.FCurve.ModuleSheafTensor

variable {X : Scheme.{u}}

instance tensoring_preservesColimits (N : X.Modules) : PreservesColimits (tensoring N) :=
  (adjunction N).leftAdjoint_preservesColimits

instance map_epi_left {M N : X.Modules} (f : M ⟶ N) [Epi f] (P : X.Modules) :
    Epi (ModuleSheafTensor.map f (𝟙 P)) :=
  inferInstanceAs (Epi ((tensoring P).map f))

variable {A B C D P : X.Modules}

/-- Factor a tensor morphism through the cokernel in its first variable. -/
def cokernelDescLeft (f : A ⟶ B) (N : X.Modules) (k : tensor B N ⟶ P)
    (h : ModuleSheafTensor.map f (𝟙 N) ≫ k = 0) : tensor (cokernel f) N ⟶ P :=
  (PreservesCokernel.iso (tensoring N) f).hom ≫ cokernel.desc _ k h

/-- First-variable descent preserves the quotient projection. -/
@[reassoc (attr := simp)]
lemma cokernelDescLeft_projection (f : A ⟶ B) (N : X.Modules) (k : tensor B N ⟶ P)
    (h : ModuleSheafTensor.map f (𝟙 N) ≫ k = 0) :
    ModuleSheafTensor.map (cokernel.π f) (𝟙 N) ≫ cokernelDescLeft f N k h = k := by
  change (tensoring N).map (cokernel.π f) ≫
    ((PreservesCokernel.iso (tensoring N) f).hom ≫
      cokernel.desc ((tensoring N).map f) k h) = k
  rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

/-- Symmetry transports tensor maps by swapping their factors. -/
@[reassoc]
lemma map_comm {M N M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    ModuleSheafTensor.map f g ≫ (comm M' N').hom =
      (comm M N).hom ≫ ModuleSheafTensor.map g f := by
  apply hom_ext
  intro U m n
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, comm_hom_pure]

instance map_epi_right (M : X.Modules) (f : A ⟶ B) [Epi f] :
    Epi (ModuleSheafTensor.map (𝟙 M) f) := by
  have : Epi (ModuleSheafTensor.map (𝟙 M) f ≫ (comm M B).hom) := by
    rw [map_comm]
    infer_instance
  exact (epi_comp_iff_of_isIso (ModuleSheafTensor.map (𝟙 M) f) (comm M B).hom).mp this

instance (priority := 900) map_epi (f : A ⟶ B) (g : C ⟶ D) [Epi f] [Epi g] :
    Epi (ModuleSheafTensor.map f g) := by
  have he : ModuleSheafTensor.map f g =
      ModuleSheafTensor.map f (𝟙 C) ≫ ModuleSheafTensor.map (𝟙 B) g := by
    rw [← map_comp]; simp
  rw [he]
  infer_instance

/-- Factor a tensor morphism through the cokernel in its second variable. -/
def cokernelDescRight (M : X.Modules) (g : C ⟶ D) (k : tensor M D ⟶ P)
    (h : ModuleSheafTensor.map (𝟙 M) g ≫ k = 0) : tensor M (cokernel g) ⟶ P :=
  (comm M (cokernel g)).hom ≫ cokernelDescLeft g M ((comm D M).hom ≫ k) (by
    rw [← Category.assoc, map_comm, Category.assoc, h, comp_zero])

/-- Second-variable descent preserves the quotient projection. -/
@[reassoc (attr := simp)]
lemma cokernelDescRight_projection (M : X.Modules) (g : C ⟶ D)
    (k : tensor M D ⟶ P) (h : ModuleSheafTensor.map (𝟙 M) g ≫ k = 0) :
    ModuleSheafTensor.map (𝟙 M) (cokernel.π g) ≫ cokernelDescRight M g k h = k := by
  rw [cokernelDescRight, ← Category.assoc, map_comm, Category.assoc,
    cokernelDescLeft_projection, ← Category.assoc]
  have he : (comm M D).hom ≫ (comm D M).hom = 𝟙 _ := by
    apply hom_ext
    intro U m n
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, comm_hom_pure,
      Hom.id_app, ConcreteCategory.id_apply]
  rw [he, Category.id_comp]

/-- After descending on the left, a right-hand relation still vanishes. -/
lemma cokernelDescLeft_relation (f : A ⟶ B) (g : C ⟶ D) (k : tensor B D ⟶ P)
    (hf : ModuleSheafTensor.map f (𝟙 D) ≫ k = 0)
    (hg : ModuleSheafTensor.map (𝟙 B) g ≫ k = 0) :
    ModuleSheafTensor.map (𝟙 (cokernel f)) g ≫ cokernelDescLeft f D k hf = 0 := by
  apply (cancel_epi (ModuleSheafTensor.map (cokernel.π f) (𝟙 C))).mp
  rw [comp_zero, ← Category.assoc, ← map_comp]
  simp only [Category.comp_id, Category.id_comp]
  have he : ModuleSheafTensor.map (cokernel.π f) g =
      ModuleSheafTensor.map (𝟙 B) g ≫ ModuleSheafTensor.map (cokernel.π f) (𝟙 D) := by
    rw [← map_comp]; simp
  rw [he, Category.assoc, cokernelDescLeft_projection, hg]

/-- Descend an actual tensor pairing through both actual cokernels. -/
def cokernelDesc (f : A ⟶ B) (g : C ⟶ D) (k : tensor B D ⟶ P)
    (hf : ModuleSheafTensor.map f (𝟙 D) ≫ k = 0)
    (hg : ModuleSheafTensor.map (𝟙 B) g ≫ k = 0) :
    tensor (cokernel f) (cokernel g) ⟶ P :=
  cokernelDescRight (cokernel f) g (cokernelDescLeft f D k hf)
    (cokernelDescLeft_relation f g k hf hg)

/-- Double descent retains the original pairing on representatives. -/
@[reassoc (attr := simp)]
lemma cokernelDesc_projection (f : A ⟶ B) (g : C ⟶ D) (k : tensor B D ⟶ P)
    (hf : ModuleSheafTensor.map f (𝟙 D) ≫ k = 0)
    (hg : ModuleSheafTensor.map (𝟙 B) g ≫ k = 0) :
    ModuleSheafTensor.map (cokernel.π f) (cokernel.π g) ≫ cokernelDesc f g k hf hg = k := by
  have he : ModuleSheafTensor.map (cokernel.π f) (cokernel.π g) =
      ModuleSheafTensor.map (cokernel.π f) (𝟙 D) ≫
        ModuleSheafTensor.map (𝟙 (cokernel f)) (cokernel.π g) := by
    rw [← map_comp]; simp
  rw [he, Category.assoc, cokernelDesc, cokernelDescRight_projection,
    cokernelDescLeft_projection]

end FLT.Mazur.FCurve.ModuleSheafTensor
