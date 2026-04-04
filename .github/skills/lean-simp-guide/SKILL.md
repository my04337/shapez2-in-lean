---
name: lean-simp-guide
description: >
  Lean 4 の simp 系タクティク（simp, simp only, simp_all, simpa, dsimp）の使い分けと、
  simp → simp only への安定化移行を支援する。@[simp] 属性の設計基準も提供する。
  Use when: simp usage, simp only, simp stabilization, simp lemma, simp vs dsimp,
  simp_all, simpa, simp attribute, simp not working, simp too slow, simp loop,
  stabilize simp, replace simp with simp only.
metadata:
  argument-hint: 'simp 系タクティクの使い分けと安定化を支援します'
---

# simp ガイドスキル

simp 系タクティクの選択判断と `simp only` への安定化移行を支援する。

---

## simp 系タクティク一覧

| タクティク | 何をするか | 閉じるか | 用途 |
|---|---|---|---|
| `simp` | `@[simp]` DB 全体で書き換え | ✓ 可能 | **探索用** — 最終証明では避ける |
| `simp only [l₁, l₂]` | 指定補題のみで書き換え | ✓ 可能 | **最終証明用** — 再現性が高い |
| `dsimp` | 定義的簡約のみ（証明項を生成しない） | ✓ 可能 | 軽量・高速。`simp` 前の下準備 |
| `dsimp only [l₁]` | 指定補題の定義的簡約のみ | ✓ 可能 | `dsimp` の安定版 |
| `simp_all` | 全仮定 + ゴールを一括簡約 | ✓ 可能 | 仮定も含めて一掃したい場合 |
| `simpa` | `simp` + `using e` で仕上げ | ✓ 必ず | ゴール + 仮定を simp してから term で閉じる |
| `simp?` | `simp` を実行して使った補題リストを表示 | — | **開発用** — `simp only` への移行ツール |

---

## 判断フロー

```
ゴールを簡約したい
│
├─ 開発中・探索フェーズ
│   └─ `simp` で試す → 成功したら `simp?` で補題リストを取得
│       └─ `simp only [...]` に置換して安定化
│
├─ 定義的等式のみ（ベータ簡約・let 展開等）
│   └─ `dsimp` / `dsimp only [...]`
│
├─ 仮定も含めて全部簡約したい
│   └─ `simp_all` / `simp_all only [...]`
│
├─ `simp` + 仮定 `h` で仕上げたい
│   └─ `simpa using h`
│       ▸ `simpa [lemma1] using h` で補題追加も可
│
└─ ゴールの一部だけ simp したい
    └─ `conv => ... simp only [...]` で部分適用
```

---

## `simp?` → `simp only` 安定化手順

### 手動手順

1. 証明中の `simp` を `simp?` に一時変更
2. Lean Language Server または REPL で `Try this:` メッセージを確認
3. 提案された `simp only [lemma1, lemma2, ...]` で置換

### REPL による自動化

REPL スクリプトが `import S2IL + Mathlib.Tactic` を自動プレペンドするため、JSONL 内では `"env": 0` を直接使える。

```jsonl
{"cmd": "theorem foo (l : List Nat) : (l ++ []).length = l.length := by simp?", "env": 0}
```

▶ 応答例:

```json
{"messages":[{"severity":"info","data":"Try this:\n  [apply] simp only [List.append_nil]"}],"env":1}
```

`data` フィールドの `[apply]` 行から `simp only [...]` 部分を抽出して置換する。

### `simp_all?` の場合

```jsonl
{"cmd": "theorem foo (l : List Nat) (h : l = []) : l.length = 0 := by simp_all?", "env": 0}
```

▶ 応答例: `"Try this:\n  [apply] simp_all only [List.length_nil]"`

---

## `@[simp]` 属性の設計基準

### 登録すべきもの

- **正規形への書き換え**: `List.length_nil`, `Nat.add_zero`, `Bool.not_not`
- **コンストラクタ射影**: `Prod.fst_mk`, `Option.some_get`
- **条件付きで常に有用**: `List.map_map`, `Function.comp_id`

### 登録すべきでないもの

- **条件付き等式**（`h : P → a = b` 形式の補題）— simp ループの原因になる
- **方向が曖昧な等式**（`a + b = b + a`）— 無限ループ
- **大きな展開**（定義 body が大きいもの）— ゴールが肥大化

### ルール

```
@[simp] の補題は：
  ✓ 左辺が右辺より「複雑」であること（正規化方向）
  ✓ 条件なしで適用可能であること（理想）
  ✓ 他の @[simp] 補題と矛盾しないこと
  ✗ a = a のトートロジーは不要
  ✗ 両方向に @[simp] を付けない
```

---

## simp が期待通り動かない場合

| 症状 | 原因 | 対処 |
|---|---|---|
| simp が何もしない | 必要な補題が `@[simp]` でない | `simp only [specific_lemma]` で明示 |
| simp が遅い/タイムアウト | DB が巨大 / ループ | `simp only` で絞る / `set_option maxHeartbeats` |
| simp でゴールが複雑化 | 不適切な書き換え方向 | `simp only [-bad_lemma]` で除外 |
| simp ループ | 双方向に書き換え可能な補題 | 片方を `@[simp]` から外す |
| `simp` は閉じるが `simp only` で再現できない | `@[simp]` DB に暗黙の補題がある | `simp?` で確認 / Mathlib 更新時に再確認 |

---

## simp の高度なオプション

| オプション | 効果 | 例 |
|---|---|---|
| `simp only [...]` | 指定補題のみ使用 | `simp only [Nat.add_zero]` |
| `simp [...]` | DB + 追加補題 | `simp [myLemma]` |
| `simp [-lemma]` | 特定補題を除外 | `simp [-Nat.add_comm]` |
| `simp at h` | 仮定 `h` に適用 | `simp at h` |
| `simp at h ⊢` | 仮定とゴール両方 | `simp [foo] at h ⊢` |
| `simp at *` | 全仮定 + ゴール | ≈ `simp_all` だが挙動が微妙に異なる |
| `simp (config := ...)` | 細かい設定 | `simp (config := { contextual := true })` |

---

## Gotchas

- `simp` の結果は Mathlib バージョンアップで変わる。最終証明では必ず `simp only [...]` を使う
- `simp_all` は仮定を書き換えるため、後続タクティクで仮定名が変わることがある
- `dsimp` は証明項を生成しないため term-mode のゴール変更に便利（`change` の代替）
- `simpa using h` は `h` の型も simp するため、`h` の型が simp で変わることに注意

## 関連

- **lean-tactic-select** — ゴール形状からタクティクを選択
- **lean-simp-stabilizer** サブエージェント — simp → simp only の自動安定化
