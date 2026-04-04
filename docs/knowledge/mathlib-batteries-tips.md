# Mathlib / Batteries 活用ノウハウ

本プロジェクト (S2IL) で Mathlib・Batteries を利用する際に得られた実践的な知見。

---

## 依存関係の構造

> **補題カタログと置換パターン**: 発見済み補題・手動定義との置換パターンは [`.github/skills/lean-mathlib-search/references/batteries-catalog.md`](../../.github/skills/lean-mathlib-search/references/batteries-catalog.md) を参照。新規補題の探索には **lean-mathlib-search** スキル（または **lean-lemma-finder** エージェント）を使う（[`mathlib-search-guide.md`](../../.github/skills/lean-mathlib-search/references/mathlib-search-guide.md)）。

- `lakefile.toml` で **Mathlib** に依存 → Batteries は Mathlib に内包される
- `import Batteries` で Batteries 単体をインポートできる（Mathlib 全体より軽量）
- 特定モジュールだけ必要な場合は `import Batteries` で十分なことが多い

---

## `simp` 最適化のノウハウ

### `@[simp]` 属性を活用した `simp only` の簡略化

Layer レベルの定理に `@[simp]` が付いていれば、Shape レベルの証明で明示的に参照する必要はない。

```lean
-- ❌ 冗長: Layer 版を明示参照
ext; simp [rotateCW, mapLayers, List.map_map, Layer.rotateCW_four]

-- ✅ 簡潔: @[simp] で自動適用
ext; simp [rotateCW, mapLayers, List.map_map]
```

### `simp only` vs `simp` の使い分け

- `simp only [...]`: 適用する補題を完全に制御。再現性が高い。
- `simp [...]`: `@[simp]` タグ付き補題も自動適用。証明が短くなるが脆い。
- **本プロジェクトの方針**: 証明の安定性を重視し `simp only` を基本とする。ただし単純な等式のクロージングには `simp` もOK。

---

## `List.Perm` は core Lean 4 に存在する

`List.Perm` はリストの置換（permutation）を表す帰納型で、
Mathlib なしで core Lean 4 に含まれている。

コンストラクタ:

| コンストラクタ | 意味 |
|---|---|
| `nil` | 空リスト同士の置換 |
| `cons x` | 先頭が同じ要素 |
| `swap x y` | 先頭 2 要素の交換 |
| `trans` | 推移律 |

リスト順序に依存しない集合論的等価性（BFS 探索順序の違いを吸収する等）を述べる際に活用できる。

---

## `decide` と `omega` の注意事項

### `decide` が使えない場面

- `∀ (a : Color), ...` のような全称命題で `Fintype Color` がない場合
- → `cases a <;> rfl` で代替。`Fintype` 導入のオーバーヘッドは現時点では不要

### `omega` の守備範囲

- `Nat` / `Int` の線形不等式に強い（プロジェクト内 50+ 箇所で使用）
- `List.length` 関連の不等式の自動証明に有効
- `Direction` を `Fin 4` にすれば回転の証明にも使えるが、破壊的変更のため保留

---

## 型クラスインスタンスの登録パターン

### 有限帰納型に対する `Std.Commutative` 等の登録

```lean
-- 1. 元となる定理を証明
theorem mix_comm (a b : Color) : mix a b = mix b a := by
    cases a <;> cases b <;> rfl

-- 2. 型クラスインスタンスとして登録
instance : Std.Commutative Color.mix where
    comm := mix_comm
```

**メリット**: `Std.Commutative.comm` が型クラス推論で自動的に利用可能になる。
将来 `simp` タグに登録するライブラリ補題がこのインスタンスを前提とする場合に備える。

### 非結合的な演算の注意

`Semigroup` / `Monoid` は結合法則を要求する。
`Color.mix` は `mix_not_assoc` で非結合的なので、これらの型クラスは使えない。
`Std.Commutative` + `Std.IdempotentOp` + `Std.LawfulIdentity` の組み合わせで十分。

---

## `Finset` の設計制約

### `Finset.toList` は noncomputable

`Finset α → List α` の変換は **noncomputable** である。
`Finset` の内部表現が `Multiset`（`Quot (List.Perm)`）であり、具体的なリストを取り出すには代表元選択（逆関数）が必要なため。

| 方向 | 計算可能性 | 関数 |
|------|-----------|------|
| `List α → Finset α` | computably 可能 (`List.dedup` で構築) | `List.toFinset` |
| `Finset α → List α` | **noncomputable** | `Finset.toList` |

**設計上の教訓**: `Finset` はあくまで **証明用の抽象** であり、`#eval` や計算可能な定義では `List` を直接使い、証明時のみ `List.toFinset` で `Finset` に変換するのが現実的。`Finset.toList` を計算可能なコードで使おうとすると `noncomputable` エラーになる。

### `Fintype QuarterPos` は存在しない

`QuarterPos` の要素数はゲーム設定 (`GameConfig.layerCount`) に依存する。
グローバルな `Fintype QuarterPos` インスタンスは存在しないため、以下の Mathlib API は直接使えない:

| API | 要求する制約 | 回避策 |
|-----|------------|--------|
| `SimpleGraph.reachableSet` | `Fintype V` | `List.toFinset` でラップした独自実装を使う |
| `Finset.univ : Finset QuarterPos` | `Fintype QuarterPos` | `(QuarterPos.allValid s).toFinset` を使う |
