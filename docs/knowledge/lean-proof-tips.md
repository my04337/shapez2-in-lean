# Lean 4 証明 Tips

本プロジェクトの開発で得られた Lean 4 の証明に関する一般的なノウハウ。

---

## String 型の証明における注意点

Lean 4 の `String` 型は内部が UTF-8 バイト列であり、多くの関数がカーネルレベルで最適化されている。定理証明では以下の制約がある。

### 展開不可能な関数一覧

| 関数 | 理由 | 代替手段 |
|---|---|---|
| `String.splitOn` | 内部で `@[irreducible] String.splitOnAux` を使用 | 自前の `List Char` ベース split 関数 |
| `String.intercalate` | 内部ヘルパー `go✝`（ハイジェニック名）が展開不可 | `List Char` で結合 → `String.ofList` |

### `String` ↔ `List Char` ブリッジの活用

証明が必要な場合は `List Char` レベルに落として操作し、以下の stdlib 補題でブリッジする:

```lean
-- String → List Char → String のラウンドトリップ
String.ofList_toList : String.ofList s.toList = s
-- List Char → String → List Char のラウンドトリップ
String.toList_ofList : (String.ofList l).toList = l
```

詳細は [`string-roundtrip-proof.md`](string-roundtrip-proof.md) を参照。

---

## タクティクの使い分け

### `decide` — 有限型の全パターン網羅

有限の列挙型に関する命題は `decide` で自動証明できる。`cases` で分解した後の個別ケースにも有効。

```lean
-- 各色の具体的な文字が ':' でないことの証明
private theorem Quarter.toString_noColon (q : Quarter) :
        ':' ∉ q.toString.toList := by
    cases q with
    | empty => decide
    | pin => decide
    | crystal c => cases c <;> decide          -- 全色を展開して decide
    | colored p c => cases p <;> cases c <;> decide  -- 全パーツ×全色を展開
```

### `rw` vs `simp only` — 適材適所

| タクティク | 適するケース | 不向きなケース |
|---|---|---|
| `rw` | 適用順序を厳密に制御したい場合。左辺が一意にマッチする場合 | match 式内部の複数箇所に散在するパターン |
| `simp only` | 複数の同種パターンを一括で解決したい場合 | 適用順序が重要な場合（意図しないリライトが起きうる） |

**組み合わせパターン**: `rw` で構造を段階整理 → `simp only` で残りを一括解決

```lean
-- rw でリスト構造を整理し、simp only で Layer.ofString? を一括解決
rw [toCharList, splitOnColon_append_colon _ _ h1, splitOnColon_noColon _ h2]
simp only [Layer.ofString_ofList_toString]
```

### `<;>` — 複数ゴールへの一括適用

`cases` で分岐した後、全ケースに同じタクティクを適用する場合に便利。

```lean
-- 全コンストラクタが rfl で閉じる場合
cases s <;> rfl

-- 全コンストラクタを simp で閉じる場合
cases s <;> simp [layers]
```

---

## `List.mapM` を証明で避けるべき理由

`List.mapM` は内部で `List.mapM.loop`（アキュムレータ + `List.reverse` パターン）を使用する。
`simp` で展開すると `do` / `pure` / `.reverse` の形になり、元のパターンマッチと整合しない。

**回避策**: `mapM` を使わず、元データ構造のパターンマッチで直接処理する。

```lean
-- ❌ mapM を使う（証明困難）
match parts.mapM (fun cs => Layer.ofString? (String.ofList cs)) with
| some [l1, l2] => ...

-- ✅ 直接パターンマッチ（証明容易）
match parts with
| [c1, c2] =>
    match Layer.ofString? (String.ofList c1),
          Layer.ofString? (String.ofList c2) with
    | some l1, some l2 => ...
```

---

## 帰納法による `List` の証明パターン

`List` に関する定理は `induction` + `cons` ケースでの `have` による前提整理が基本。

```lean
private theorem splitOnColon_noColon (cs : List Char) (h : ':' ∉ cs) :
        splitOnColon cs = [cs] := by
    induction cs with
    | nil => rfl
    | cons c rest ih =>
        -- ① 先頭要素が ':' でないことを抽出
        have hc : c ≠ ':' := by intro heq; exact h (heq ▸ .head _)
        -- ② 残りのリストに ':' が含まれないことを抽出
        have hrest : ':' ∉ rest := by intro hmem; exact h (.tail _ hmem)
        -- ③ 定義を展開し、帰納法の仮定を適用
        simp only [splitOnColon, beq_iff_eq, hc, ite_false, ih hrest]
```

ポイント:
- `List.Mem.head` と `List.Mem.tail` で `∉` を分解
- `beq_iff_eq` で `BEq` を `Eq` に変換（`if c == ':'` → `if c = ':'`）
- `ite_false` で `if False then ... else ...` を簡約

---

## `rcases` による析取（`∨`）の分解

`List.mem_append`（`x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂`）の結果を分解する際に `rcases` が便利。

```lean
-- 4つの Quarter の toString を結合した Layer.toString に ':' が含まれないことの証明
private theorem Layer.toString_noColon (l : Layer) :
        ':' ∉ l.toString.toList := by
    simp only [Layer.toString, String.toList_append, List.mem_append]
    intro h
    -- h : ... ∨ ... ∨ ... ∨ ... を4分岐に分解
    rcases h with ((h | h) | h) | h
    · exact Quarter.toString_noColon l.ne h
    · exact Quarter.toString_noColon l.se h
    · exact Quarter.toString_noColon l.sw h
    · exact Quarter.toString_noColon l.nw h
```
