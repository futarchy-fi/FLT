/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Compactness of finite unions of compact open images

The literal source schemes cover their open image union. Finiteness and
compactness of those sources therefore prove compactness of the union.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur

universe u v

variable {X : Scheme.{u}} {ι : Type v} [Finite ι] {V : ι → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] [hV : ∀ i, CompactSpace (V i)]

/-- A finite open image union of compact schemes is compact. -/
instance openImageUnion_compactSpace : CompactSpace (openImageUnion f).toScheme := by
  let _ : Finite (openImageUnionCover f).I₀ := inferInstanceAs (Finite ι)
  let _ (i : (openImageUnionCover f).I₀) :
      CompactSpace ((openImageUnionCover f).X i) := hV i
  exact (openImageUnionCover f).compactSpace

/-- The corresponding open subset of the ambient scheme is compact. -/
theorem openImageUnion_isCompact : IsCompact (openImageUnion f : Set X) := by
  exact isCompact_iff_compactSpace.mpr (openImageUnion_compactSpace f)

end FLT.Mazur
