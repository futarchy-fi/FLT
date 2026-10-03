/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.KernelCocycleDescent

/-!
# Cochain descent to the image of a subgroup

The restricted bounding cochain descends to the image subgroup in the same
finite quotient as the ambient cocycle. Their boundary equation is preserved.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G H M P : Type*} [Group G] [Group H]

/-- The surjection from a subgroup onto its image. -/
def subgroupImageHom (f : G →* H) (N : Subgroup G) : N →* N.map f where
  toFun n := ⟨f n, ⟨n, n.property, rfl⟩⟩
  map_one' := Subtype.ext f.map_one
  map_mul' g h := Subtype.ext (f.map_mul g h)

/-- Every image-subgroup element has a lift in the original subgroup. -/
theorem subgroupImageHom_surjective (f : G →* H) (N : Subgroup G) :
    Function.Surjective (subgroupImageHom f N) := by
  rintro ⟨q, n, hn, rfl⟩
  exact ⟨⟨n, hn⟩, rfl⟩

/-- Descend a subgroup cochain along fibers, together with its coefficient descent. -/
theorem exists_descended_subgroup_cochain (f : G →* H) (N : Subgroup G)
    (i : P → M) (b : N → M)
    (hfib : ∀ n m : N, f n = f m → b n = b m) (hval : ∀ n, ∃ p, i p = b n) :
    ∃ d : N.map f → P, ∀ n, i (d (subgroupImageHom f N n)) = b n := by
  classical
  let s := (subgroupImageHom_surjective f N).hasRightInverse.choose
  have hs : Function.RightInverse s (subgroupImageHom f N) :=
    (subgroupImageHom_surjective f N).hasRightInverse.choose_spec
  refine ⟨fun q => (hval (s q)).choose, fun n => ?_⟩
  calc
    _ = b (s (subgroupImageHom f N n)) := (hval _).choose_spec
    _ = b n := hfib _ _ (congrArg Subtype.val (hs (subgroupImageHom f N n)))

variable [AddCommGroup M] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction H P]

/-- A cocycle constant on quotient fibers descends with its coefficients. -/
theorem exists_twoCocycle_descent_of_fibers (f : G →* H) (hf : Function.Surjective f)
    (i : P →+ M) (hi : Function.Injective i) (heq : ∀ g p, i (f g • p) = g • i p)
    (c : G × G → M) (hc : IsCocycle₂ c)
    (hfib : ∀ g h g' h', f g = f g' → f h = f h' → c (g, h) = c (g', h'))
    (hval : ∀ g h, ∃ p, i p = c (g, h)) :
    ∃ d : H × H → P, IsCocycle₂ d ∧ ∀ g h, i (d (f g, f h)) = c (g, h) := by
  classical
  obtain ⟨s, hs, _⟩ := exists_normalized_section f hf
  let d : H × H → P := fun q => (hval (s q.1) (s q.2)).choose
  have hd (g h : G) : i (d (f g, f h)) = c (g, h) :=
    (hval _ _).choose_spec.trans (hfib _ _ _ _ (hs _) (hs _))
  refine ⟨d, ?_, hd⟩
  intro g h j
  obtain ⟨g, rfl⟩ := hf g
  obtain ⟨h, rfl⟩ := hf h
  obtain ⟨j, rfl⟩ := hf j
  apply hi
  simp only [map_add, heq, ← map_mul, hd]
  exact hc g h j

/-- Simultaneous descent preserves the restricted bounding equation. -/
theorem descended_subgroup_boundary (f : G →* H) (N : Subgroup G)
    (i : P →+ M) (hi : Function.Injective i) (heq : ∀ g p, i (f g • p) = g • i p)
    (c : G × G → M) (b : N → M)
    (hb : ∀ n m : N, c (n, m) = n • b m - b (n * m) + b n)
    (d : H × H → P) (hd : ∀ g h, i (d (f g, f h)) = c (g, h))
    (a : N.map f → P) (ha : ∀ n, i (a (subgroupImageHom f N n)) = b n) :
    ∀ n m : N.map f, d (n, m) = n • a m - a (n * m) + a n := by
  intro n m
  obtain ⟨n, rfl⟩ := subgroupImageHom_surjective f N n
  obtain ⟨m, rfl⟩ := subgroupImageHom_surjective f N m
  apply hi
  change i (d (f n, f m)) = i (f n • a (subgroupImageHom f N m) -
    a (subgroupImageHom f N n * subgroupImageHom f N m) + a (subgroupImageHom f N n))
  rw [map_add, map_sub, heq, ← map_mul, ha, ha, ha, hd]
  exact hb n m

end LocalClassFieldTheory
