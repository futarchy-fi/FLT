/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassCoefficientShearStageIso
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Retained line origins under a change of stage expression

The canonical stage comparison preserves the entire retained line, hence its
original origin. Both the stage and retained index may have different expressions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q (Data.b6 d)
variable (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "h2" => coefficientShear_a₂_zero W S r hr

variable (k : ℕ) (hk : k ≤ n) (e : t = k) (i' : Fin k) (hi : i.val = i'.val)
  (hs' : algebraMap R S (π ^ (start + i'.val)) = 0)
  (h3' : algebraMap R S (data ⟨i'.val + 1, by omega⟩).b3 = 0)
  (h4' : algebraMap R S (data ⟨i'.val + 1, by omega⟩).b4 = 0)
  (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)

/-- Reindexing preserves the complete retained line with its original slope and parameter. -/
@[reassoc] theorem coefficientShearRetainedLine_stageIso :
    coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr v hv ≫
        (coefficientShearStageIso hπ data S r t k ht hk e).hom =
      coefficientShearRetainedLine hπ data S r k hk i' hs' hp h3' h4' hr v hv := by
  subst k
  have h : i = i' := Fin.ext hi
  subst i'
  exact Category.comp_id _

end FLT.Mazur.WeierstrassDividedDepth
