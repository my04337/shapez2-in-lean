-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape

/-!
# S2IL.Kernel.BFS

汎用 BFS と到達可能性 `GenericReachable`。

## 公開 API

- `genericBfs` — エッジ述語をパラメータとする汎用 BFS
- `GenericReachable` — BFS に対応する到達可能性述語
- 健全性・完全性・不変条件保存定理群

## Internal

- `S2IL.Kernel.Internal.BFSImpl` — 実装補助補題
-/

namespace S2IL

/-- 汎用 BFS: 任意のエッジ述語 `edge` に対して到達可能ノードを列挙する。 -/
axiom genericBfs {α : Type _} [BEq α]
    (edge : α → α → Bool) (allNodes visited queue : List α) (fuel : Nat) : List α

/-- 汎用到達可能性：エッジ述語 `edge` で `start → ... → target` と辿れる。 -/
axiom GenericReachable {α : Type _} (edge : α → α → Bool) : α → α → Prop

namespace GenericReachable

axiom refl {α : Type _} {edge : α → α → Bool} (a : α) :
    GenericReachable edge a a

axiom step {α : Type _} {edge : α → α → Bool} {a b c : α} :
    GenericReachable edge a b → edge b c = true → GenericReachable edge a c

axiom trans {α : Type _} {edge : α → α → Bool} {a b c : α} :
    GenericReachable edge a b → GenericReachable edge b c → GenericReachable edge a c

axiom symm {α : Type _} {edge : α → α → Bool} {a b : α}
    (hsymm : ∀ x y, edge x y = edge y x) :
    GenericReachable edge a b → GenericReachable edge b a

axiom mono {α : Type _} {edge1 edge2 : α → α → Bool} {s p : α} :
    (∀ a b, edge1 a b = true → edge2 a b = true) →
    GenericReachable edge1 s p → GenericReachable edge2 s p

end GenericReachable

/-- BFS 健全性：出力されたノードは到達可能。 -/
axiom genericBfs_sound {α : Type _} [BEq α] [LawfulBEq α]
    (edge : α → α → Bool) (allNodes vis queue : List α) (fuel : Nat) (p : α) :
    (genericBfs edge allNodes vis queue fuel).any (· == p) = true →
    vis.any (· == p) = true ∨
    ∃ q, queue.any (· == q) = true ∧ GenericReachable edge q p

/-- BFS 完全性：到達可能なノードは出力に含まれる。 -/
axiom genericBfs_complete {α : Type _} [BEq α] [LawfulBEq α]
    (edge : α → α → Bool) (allNodes : List α) (start p : α) (fuel : Nat) :
    fuel ≥ allNodes.length →
    allNodes.any (· == p) = true →
    GenericReachable edge start p →
    (genericBfs edge allNodes [] [start] fuel).any (· == p) = true

end S2IL
