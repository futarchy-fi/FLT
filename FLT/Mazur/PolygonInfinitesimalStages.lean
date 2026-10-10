/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalMarkings
public import FLT.Mazur.PolygonInfinitesimalSeparated

/-!
# Concrete finite-order polygon smoothing stages

At order m the coefficient ring is R[q]/(q^(m+1)), with its actual nilpotent
parameter q. The cyclic construction gives a flat separated marked family at
every order. Successive coefficient restrictions retain q. Compatibility of
the assembled families under these restrictions is a subsequent construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The concrete coefficient algebra of the mth infinitesimal smoothing stage. -/
abbrev Ring := AdjoinRoot ((X : R[X]) ^ (m + 1))

/-- The actual smoothing parameter in the truncated polynomial coefficient ring. -/
def parameter : Ring R m := AdjoinRoot.root _

/-- The defining coefficient relation gives nilpotence of the actual parameter. -/
theorem parameter_pow : parameter R m ^ (m + 1) = 0 := by
  simpa only [parameter, Polynomial.eval₂_pow, Polynomial.eval₂_X] using
    AdjoinRoot.eval₂_root ((X : R[X]) ^ (m + 1))

instance parameter_nilpotent : Fact (IsNilpotent (parameter R m)) :=
  ⟨m + 1, parameter_pow R m⟩

/-- The successive coefficient restriction sends the new parameter to the previous one. -/
def restriction : Ring R (m + 1) →ₐ[R] Ring R m :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (parameter R m) (by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_succ, parameter_pow, zero_mul])

/-- Successive coefficient restrictions preserve the specified smoothing parameter. -/
@[simp] theorem restriction_parameter :
    restriction R m (parameter R (m + 1)) = parameter R m := by
  simp [restriction, parameter, AdjoinRoot.liftAlgHom]

variable (n : ℕ) (h : 2 ≤ n)

/-- The actual cyclic family over the mth truncated polynomial base. -/
def family : Over (Spec (.of (Ring R m))) :=
  PolygonInfinitesimal.family (Ring R m) (parameter R m) n h

instance family_flat : Flat (family R m n h).hom :=
  PolygonInfinitesimal.toBase_flat _ _ n h

instance family_locallyOfFinitePresentation : LocallyOfFinitePresentation (family R m n h).hom :=
  PolygonInfinitesimal.toBase_locallyOfFinitePresentation _ _ n h

instance family_quasiCompact : QuasiCompact (family R m n h).hom :=
  PolygonInfinitesimal.toBase_quasiCompact _ _ n h

instance family_separated : IsSeparated (family R m n h).hom :=
  PolygonInfinitesimalSeparated.separated _ _ n h

/-- The unit-one marking on each cyclic chart of the concrete finite-order family. -/
def marking (i : Fin n) : Spec (.of (Ring R m)) ⟶ (family R m n h).left :=
  PolygonInfinitesimal.marking (Ring R m) (parameter R m) n h i 1

/-- The concrete stage markings are actual sections over their truncated base. -/
@[reassoc] theorem marking_base (i : Fin n) :
    marking R m n h i ≫ (family R m n h).hom = 𝟙 _ :=
  PolygonInfinitesimal.marking_base _ _ n h i 1

/-- The concrete stage has one pairwise disjoint marked section for each cyclic index. -/
theorem markings_pairwise :
    Pairwise (fun i j ↦ Disjoint (Set.range (marking R m n h i))
      (Set.range (marking R m n h j))) :=
  PolygonInfinitesimal.pairwise_markings _ _ n h (fun _ ↦ 1)

end FLT.Mazur.PolygonInfinitesimalStages
