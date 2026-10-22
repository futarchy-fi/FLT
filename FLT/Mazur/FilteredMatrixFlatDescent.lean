/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredMatrixInnerInverse
public import FLT.Mazur.MatrixCokernelFlatCertificate

/-!
# Uniform finite-stage flatness for finite module presentations

A fixed finite presentation matrix whose cokernel is flat at the colimit
has a flat cokernel at one later stage. Every further scalar change preserves
that flatness. Unlike finite relation tests, this controls all relations at
one stage. Finite presentation as an algebra alone does not supply the finite
module presentation required here.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.Approximation
section
variable {R S : Type*} [CommRing R] [CommRing S]
  {m n : Type*} [Finite m] [Fintype n]

/-- The finite certificate proves flatness after any change of coefficients. -/
theorem matrix_cokernel_flat_map (A : Matrix m n R)
    [Module.Flat R ((m → R) ⧸ LinearMap.range A.mulVecLin)] (φ : R →+* S) :
    Module.Flat S ((m → S) ⧸ LinearMap.range (A.map φ).mulVecLin) := by
  let _ := Fintype.ofFinite m
  obtain ⟨B, hB⟩ := MatrixCokernel.exists_innerInverse_of_flat A
  exact MatrixCokernel.flat_of_innerInverse (A.map φ) (B.map φ)
    (by simpa only [Matrix.map_mul] using congrArg (fun C ↦ C.map φ) hB)

end

open CategoryTheory Limits
universe u v w
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat)]
  {m n : Type*} [Finite m] [Fintype n]

include hc in
/-- Flatness of a finite matrix cokernel descends uniformly, including all further stages. -/
theorem exists_flat_matrix_stage (i : I) (A : Matrix m n (F.obj i))
    (h : Module.Flat c.pt ((m → c.pt) ⧸
      LinearMap.range (A.map (c.ι.app i).hom).mulVecLin)) :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k),
      Module.Flat (F.obj k) ((m → F.obj k) ⧸
        LinearMap.range (A.map (F.map (g ≫ e)).hom).mulVecLin) := by
  let _ := Fintype.ofFinite m
  let A₀ : Matrix m n c.pt := A.map (c.ι.app i).hom
  let _ : Module.Flat c.pt ((m → c.pt) ⧸ LinearMap.range A₀.mulVecLin) := h
  obtain ⟨B, hB⟩ := MatrixCokernel.exists_innerInverse_of_flat A₀
  obtain ⟨j, g, D, hD⟩ := exists_matrix_innerInverse_stage F c hc i A B hB
  refine ⟨j, g, fun k e ↦ ?_⟩
  let _ := MatrixCokernel.flat_of_innerInverse (A.map (F.map g).hom) D hD
  have he := matrix_cokernel_flat_map (A.map (F.map g).hom) (F.map e).hom
  have ha : (A.map (F.map g).hom).map (F.map e).hom =
      A.map (F.map (g ≫ e)).hom := by
    ext x y
    change F.map e (F.map g (A x y)) = F.map (g ≫ e) (A x y)
    rw [F.map_comp]
    rfl
  rwa [ha] at he

end FLT.Mazur.Approximation
