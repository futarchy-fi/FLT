# oig35.20 refinement — `WeierstrassCurve.galoisRepresentation` (DistribMulAction, 4 sorries)

Target: `FLT/EllipticCurve/Torsion.lean` lines 105–113, commit `3035736` (main).
Read-only analysis; no build performed.

## The action being proven lawful

`galoisRepresentationSmul` (lines 100–103) defines

```lean
g • P = WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P
```

where `Affine.Point.map` (Mathlib `AlgebraicGeometry/EllipticCurve/Affine/Point.lean:797`)
is **already a bundled `AddMonoidHom`** `(W'⁄F).Point →+ (W'⁄K).Point`, defined for
`f : F →ₐ[S] K` with `W' : WeierstrassCurve R`, instances
`[Algebra R S] [Algebra S F] [IsScalarTower R S F] …`. Here `R = S = k`, `F = K = L = K`.
`E⁄K` is `WeierstrassCurve.baseChange` (scoped notation, `Affine/Basic.lean:268`).
No `VariableChange` normalization is involved — the AlgEquiv acts through its plain
`toAlgHom` coercion, and `Point.map` acts componentwise (`some x y h ↦ some (f x) (f y) _`).

Mathlib's `Point.lean` is a `module` file but everything from line 63 sits under
`@[expose] public section`, and the FLT file's own defs sit under its `@[expose] public
section` (line 23) — so **defeq unfolding across the module boundary is available**;
opacity is NOT the obstruction.

## (1) Why the suggested lemmas do not close the goals as-is

Two distinct, precise obstructions:

**(a) `S`-parameter mismatch on `map_id` (blocks `one_smul` via Mathlib's lemma).**
Mathlib's `Point.map_id : map (Algebra.ofId F F) P = P` instantiates the base
`S := F` (here `S := K`), i.e. its `map` is `@map k K K K … (Algebra.ofId K K : K →ₐ[K] K)`.
The goal's term is `@map k k K K … (↑(1 : K ≃ₐ[k] K) : K →ₐ[k] K)` — base `S := k`.
`rw`/`simp [Point.map_id]` can never fire (the head terms differ in the implicit `S`
and in `f`'s *type*), and `exact Point.map_id P` succeeds only if the unifier fully
unfolds both `map` applications down to the `Point.rec` matcher and discharges
`Algebra.ofId K K x ≟ AlgHom.id k K x` — fragile, and it additionally requires the
scrutinee in constructor form, which a bare `P` is not. The in-file
`Points.map_id` (line 85) exists precisely to restate this at `S = k` with
`AlgHom.id k K`; but the goal's hom is `↑(1 : K ≃ₐ[k] K)`, not syntactically
`AlgHom.id k K` (they are `rfl`-equal via `AlgEquiv.refl_toAlgHom`, but `rw` with
`Points.map_id` still fails syntactically).

**(b) `•` is opaque to higher-order unification (blocks `smul_zero`/`smul_add`,
and rewriting in all four).**
The goals are stated with `HSMul.hSMul`. `_root_.map_zero : ⇑?f 0 = 0` must solve
`⇑?f 0 ≟ g • 0`; the unifier will not unfold the `SMul` instance projection to
discover `?f := Affine.Point.map ↑g` (non-syntactic head, HO unification gives up).
Same for `map_add`. A `show`/`change` to the unfolded form is mandatory before any
`exact map_zero/map_add`, and DeepSeek's transcripts almost certainly omitted it.
Similarly `mul_smul` needs `↑(g * h) = (↑g).comp ↑h`, which exists in Mathlib only
as a defeq (`aut` mul is `ψ.trans ϕ`; `AlgEquiv.aut_mul` is `-isSimp`) — there is no
stated `AlgHom`-coercion lemma for products of automorphisms, so `rw [Points.map_comp]`
alone cannot bridge `map ↑(g*h)` to `(map ↑g).comp (map ↑h)`.

## (2) Auxiliaries that make each field a one-liner

None are strictly required (see (4): defeq routes close everything), but the robust
belt-and-braces auxiliaries, both `rfl`, are:

```lean
private lemma AlgEquiv.one_toAlgHom' : ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) = AlgHom.id k K := rfl
private lemma AlgEquiv.mul_toAlgHom' (g h : K ≃ₐ[k] K) :
    ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) = (g : K →ₐ[k] K).comp (h : K →ₐ[k] K) := rfl
```

(Both provable by `rfl`: `1 = refl`, `refl_toAlgHom : ↑refl = AlgHom.id` is `rfl`
(Mathlib `Algebra/Algebra/Equiv.lean:235`); `g * h = h.trans g` and `.toAlgHom`/`.comp`
have defeq-equal fields under structure eta.)

## (3) Do the auxiliaries exist elsewhere?

- `AlgEquiv.refl_toAlgHom` — EXISTS (`Equiv.lean:235`, simp) but only for `refl`, not `1`.
- `AlgEquiv.aut_one`, `AlgEquiv.aut_mul` — EXIST (simps-generated, `-isSimp`):
  `1 = refl`, `ϕ * ψ = ψ.trans ϕ`. Usable with `rw` before `refl_toAlgHom`.
- `AlgEquiv.toAlgHomHom : (A ≃ₐ[R] A) →* (A →ₐ[R] A)` — EXISTS (`Equiv.lean:734`);
  `map_one`/`map_mul` of it give the two coercion facts, modulo `AlgHom` monoid
  (`1 = AlgHom.id`, `* = comp`, both defeq). Slightly awkward to invoke.
- A stated `↑(g * h) = ↑g.comp ↑h` for AlgEquiv→AlgHom — DOES NOT EXIST by that
  shape in Mathlib; mint in-file (or rely on defeq, below).
- `Point.map_zero`, `Point.map_add` — `map_zero` EXISTS as a `rfl` lemma
  (`Point.lean:813`); `map_add` comes free since `Point.map` is an `AddMonoidHom`
  (use `map_add _ P Q` after `show`). Nothing needs minting for zero/add.
- In-file `Points.map_id` / `Points.map_comp` (lines 85, 91) — EXIST and are the
  correct `S = k` bridges; use with `AddMonoidHom.congr_fun` to get pointwise forms.

## (4) Refined packet guidance — per-field proofs

**Edit-region restriction can stay** (instance block only); no auxiliary is needed if
the defeq routes below are used. If the seat's elaborator chokes, relax to allow the
two `private` `rfl` lemmas of (2) directly above the instance.

Replacement for lines 106–112:

```lean
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
  one_smul P := by cases P <;> rfl
  mul_smul g h P := by cases P <;> rfl
  smul_zero g := rfl
  smul_add g P Q :=
    map_add (WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)) P Q
```

Why each closes:
- `one_smul`: after `cases P`, both sides are constructor-headed; `map ↑1 (some x y h)`
  reduces to `some (↑1 x) (↑1 y) _` with `↑1 x` defeq `x`; proof irrelevance finishes.
  (`Point.map`'s body is exposed, so the matcher reduces.)
- `mul_smul`: same reduction; `↑(g*h) x` and `↑g (↑h x)` are both defeq `g (h x)`.
- `smul_zero`: `map f 0 = 0` is `rfl` in Mathlib (`map_zero'` field is `rfl`).
- `smul_add`: `g • x` is defeq `⇑(Point.map ↑g) x`, so the *elaborated expected type*
  of `map_add … P Q` matches by `exact`-level defeq (the hom is supplied explicitly,
  so no HO unification is attempted).

Fallback (if `cases … rfl` fails, e.g. matcher reduction stalls):

```lean
  one_smul P := by
    show WeierstrassCurve.Affine.Point.map ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) P = P
    exact AddMonoidHom.congr_fun (WeierstrassCurve.Points.map_id (E := E) K) P
  mul_smul g h P := by
    show WeierstrassCurve.Affine.Point.map ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) P
        = WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)
            (WeierstrassCurve.Affine.Point.map (h : K →ₐ[k] K) P)
    exact (WeierstrassCurve.Affine.Point.map_map (h : K →ₐ[k] K) (g : K →ₐ[k] K) P).symm
  smul_zero g := by
    show WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) 0 = 0
    exact WeierstrassCurve.Affine.Point.map_zero _
  smul_add g P Q := by
    show WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) (P + Q)
        = WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P
          + WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) Q
    exact map_add _ P Q
```

Notes for the seat:
- The `one_smul` fallback leans on `↑1 ≟ AlgHom.id k K` being `rfl` at `exact`-time
  (this is exactly the defeq already exercised by the compiling proof of
  `Points.map_id` at line 88, which crosses the harder `S = k` vs `S = K` gap).
- In `mul_smul`, `map_map` is instantiated at `S = k` directly (`f, g : K →ₐ[k] K`),
  so the `S`-mismatch of (1)(a) never arises; only `↑(g*h) ≟ ↑g.comp ↑h` (rfl) is
  needed, discharged by `exact`'s defeq check, not by `rw`.
- Never start with `simp`/`rw` on a goal still headed by `•` — `show` first, always.
- `Points.map`/`Points.map_id` take `E` explicitly (section variable); write
  `(E := E)` or positional `E` to avoid the "function expected" confusions seen in
  failed transcripts.
