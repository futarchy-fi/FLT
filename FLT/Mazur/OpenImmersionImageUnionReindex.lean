/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnion

/-!
# Reindexing unions of open immersion images

Changing the labels of a common overlap family preserves its union and
all constituent maps. This supplies the domain transport for symmetric atlases.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur

universe u v w

variable {X : Scheme.{u}} {ι : Type v} {μ : Type w} {V : ι → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] (r : μ ≃ ι)

/-- An equivalent indexing family has the same ambient image union. -/
theorem openImageUnion_reindex : openImageUnion (fun m ↦ f (r m)) = openImageUnion f := by
  exact r.surjective.iSup_comp (fun i ↦ (f i).opensRange)

/-- Reindexing identifies the unions over the fixed ambient chart. -/
def openImageUnionReindexIso :
    (openImageUnion (fun m ↦ f (r m))).toScheme ≅ (openImageUnion f).toScheme :=
  X.isoOfEq (openImageUnion_reindex f r)

/-- The reindexing isomorphism preserves the ambient inclusion. -/
@[reassoc (attr := simp)] theorem openImageUnionReindexIso_ι :
    (openImageUnionReindexIso f r).hom ≫ (openImageUnion f).ι =
      (openImageUnion (fun m ↦ f (r m))).ι :=
  Scheme.isoOfEq_hom_ι _ _

/-- Reindexing retains each original source map. -/
@[reassoc (attr := simp)] theorem openImageUnionReindexIso_fac (m : μ) :
    openImageUnionMap (fun m ↦ f (r m)) m ≫ (openImageUnionReindexIso f r).hom =
      openImageUnionMap f (r m) := by
  apply (cancel_mono (openImageUnion f).ι).mp
  simp only [Category.assoc, openImageUnionReindexIso_ι, openImageUnionMap_fac]

end FLT.Mazur
