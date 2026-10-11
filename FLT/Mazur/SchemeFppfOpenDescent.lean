/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyCover
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Effective descent of opens along fppf covering families

The descended open is the union of actual images of the given opens.
Compatibility on scheme fiber products proves its exact pullback formula;
joint surjectivity proves uniqueness. No reducedness assumptions are used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFppfOpen
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T)

/-- Each fppf covering arrow is open. -/
theorem cover_isOpenMap (i : 𝒰.I₀) : IsOpenMap (𝒰.f i) := by
  let V : T.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  let _ : Flat (𝒰.f i) := (V.map_prop i).1
  let _ : LocallyOfFinitePresentation (𝒰.f i) := (V.map_prop i).2
  exact (𝒰.f i).isOpenMap

/-- The actual open obtained by taking the union of the covering images. -/
def descend (U : ∀ i, (𝒰.X i).Opens) : T.Opens :=
  ⨆ i, ⟨𝒰.f i '' (U i : Set (𝒰.X i)), cover_isOpenMap 𝒰 i _ (U i).isOpen⟩

/-- Membership is witnessed by a point in one original covering open. -/
theorem mem_descend (U : ∀ i, (𝒰.X i).Opens) (t : T) :
    t ∈ descend 𝒰 U ↔ ∃ i, ∃ x ∈ U i, 𝒰.f i x = t := by
  simp only [descend, TopologicalSpace.Opens.mem_iSup, TopologicalSpace.Opens.mem_mk,
    Set.mem_image, SetLike.mem_coe]

/-- Any test open with the specified fiber-product restrictions is the exact inverse image. -/
theorem preimage_descend (U : ∀ i, (𝒰.X i).Opens)
    {V : Scheme.{u}} (b : V ⟶ T) (W : V.Opens)
    (h : ∀ i, (pullback.fst (𝒰.f i) b) ⁻¹ᵁ U i =
      (pullback.snd (𝒰.f i) b) ⁻¹ᵁ W) :
    b ⁻¹ᵁ descend 𝒰 U = W := by
  ext v
  change b v ∈ descend 𝒰 U ↔ v ∈ W
  rw [mem_descend]
  constructor
  · rintro ⟨i, x, hx, he⟩
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback x v he
    have hm := SetLike.ext_iff.mp (h i) z
    change pullback.fst (𝒰.f i) b z ∈ U i ↔ pullback.snd (𝒰.f i) b z ∈ W at hm
    rw [hz, hz'] at hm
    exact hm.mp hx
  · intro hv
    let C : T.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
    obtain ⟨i, x, hx⟩ := C.exists_eq (b v)
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback x v hx
    have hm := SetLike.ext_iff.mp (h i) z
    change pullback.fst (𝒰.f i) b z ∈ U i ↔ pullback.snd (𝒰.f i) b z ∈ W at hm
    rw [hz, hz'] at hm
    exact ⟨i, x, hm.mpr hv, hx⟩

/-- Compatible original opens are recovered on each member of the covering family. -/
theorem descend_restrict (U : ∀ i, (𝒰.X i).Opens)
    (h : ∀ i j, (pullback.fst (𝒰.f i) (𝒰.f j)) ⁻¹ᵁ U i =
      (pullback.snd (𝒰.f i) (𝒰.f j)) ⁻¹ᵁ U j) (j : 𝒰.I₀) :
    (𝒰.f j) ⁻¹ᵁ descend 𝒰 U = U j :=
  preimage_descend 𝒰 U (𝒰.f j) (U j) (fun i ↦ h i j)

/-- Joint surjectivity detects equality of actual opens. -/
theorem ext (U V : T.Opens) (h : ∀ i, (𝒰.f i) ⁻¹ᵁ U = (𝒰.f i) ⁻¹ᵁ V) : U = V := by
  ext t
  let C : T.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  obtain ⟨i, x, rfl⟩ := C.exists_eq t
  exact SetLike.ext_iff.mp (h i) x

end FLT.Mazur.SchemeFppfOpen
