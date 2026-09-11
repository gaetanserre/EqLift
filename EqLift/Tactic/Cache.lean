/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public meta import Lean.Meta.SynthInstance
public meta import Std.Data.HashMap

/-!
# Cache for the lifting/unlifting transformations

Transforming an equality repeatedly synthesizes the same instances (`MeasurableSpace X`,
`IsSFiniteKernel κ`, ...) and rebuilds the same terms (measurable equivalences, types of
kernels, ...). This file provides a cache, reset at the beginning of each transformation, that
memoizes these computations.

## Main declarations

* `synthInstanceCached`: `synthInstance` with memoization.
* `inferTypeCached`: `inferType` with memoization.
* `memoized`: memoization of an arbitrary computation returning expressions, keyed by a tag and an
  expression.
* `resetTransformCache`: empties the cache.
-/

public meta section

open Lean Meta

/-- The cache of the lifting/unlifting transformations. -/
structure TransformCache where
  /-- Synthesized instances, keyed by the class application. -/
  insts : Std.HashMap Expr Expr := {}
  /-- Inferred types, keyed by the expression. -/
  types : Std.HashMap Expr Expr := {}
  /-- Memoized computations, keyed by a tag and an expression. -/
  memo : Std.HashMap (Name × Expr) (Array Expr) := {}
  deriving Inhabited

private initialize transformCacheRef : IO.Ref TransformCache ← IO.mkRef {}

/-- Empties the cache. To be called at the beginning of each transformation. -/
def resetTransformCache : MetaM Unit := transformCacheRef.set {}

/-- `synthInstance` with memoization. -/
def synthInstanceCached (type : Expr) : MetaM Expr := do
  match (← transformCacheRef.get).insts[type]? with
  | some inst => return inst
  | none =>
    let inst ← synthInstance type
    transformCacheRef.modify fun c => { c with insts := c.insts.insert type inst }
    return inst

/-- `inferType` with memoization. -/
def inferTypeCached (e : Expr) : MetaM Expr := do
  match (← transformCacheRef.get).types[e]? with
  | some type => return type
  | none =>
    let type ← inferType e
    transformCacheRef.modify fun c => { c with types := c.types.insert e type }
    return type

/-- Memoizes the computation `f`, keyed by `tag` and `key`. -/
def memoized (tag : Name) (key : Expr) (f : MetaM (Array Expr)) : MetaM (Array Expr) := do
  match (← transformCacheRef.get).memo[(tag, key)]? with
  | some res => return res
  | none =>
    let res ← f
    transformCacheRef.modify fun c => { c with memo := c.memo.insert (tag, key) res }
    return res

end
