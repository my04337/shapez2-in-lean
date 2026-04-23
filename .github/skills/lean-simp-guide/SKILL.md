---
name: lean-simp-guide
description: >
  Guide simp tactic selection and simp -> simp only stabilization in Lean 4.
  Use when: simp usage, simp only, simp stabilization, simp lemma, simp vs dsimp,
  simp_all, simpa, simp attribute, simp not working, simp too slow, simp loop,
  stabilize simp, replace simp with simp only.
metadata:
  argument-hint: 'Describe simp issue or pass file:line'
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

> **禁止**: `simp [X]` / `simp_all [X]` を直接 `simp only [X]` / `simp_all only [X]` に一括置換してはいけない。
> `simp` は明示引数に加えて `@[simp]` DB 全体を使うため、補題リストが不完全になりやすい。
> 必ず `simp?` / `simp_all?` を経由して `Try this:` の提案を取得すること。

### 手動手順

1. 証明中の `simp` を `simp?` に一時変更
2. Lean Language Server または REPL で `Try this:` メッセージを確認
3. 提案された `simp only [lemma1, lemma2, ...]` で置換

### REPL による自動化

REPL スクリプトが `import S2IL + Mathlib.Tactic + Plausible + Duper` を先頭に自動挿入するため、JSONL 内では `"env": 0` を直接使える。

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
- `simp` で閉じないが構造的に自明なゴールは `aesop` を試す。`aesop` は正規化フェーズで `simp_all` を内蔵しており、その上でルールベースの探索を行う。詳細: [`docs/lean/aesop-guide.md`](../../../docs/lean/aesop-guide.md)
- **Batteries の `@[simp]` 補題**: Batteries / Mathlib が提供する `List.map_eq_nil_iff`, `List.set_eq_nil_iff`, `List.any_filter` 等は `@[simp]` 属性を持つ場合がある。`simp only [...]` リストに含めなくても裸 `simp` では効くことがあるため、`simp?` で確認時に Batteries 補題が出現したら積極的にリストに含める。Batteries 補題カタログ: [`batteries-catalog.md`](../../lean-mathlib-search/references/batteries-catalog.md)

---

## ファイル全体のバルク安定化パイプライン

ファイル内の全 `simp` / `simp_all` を一括で `simp only` に安定化する手順。
`lean --json` フラグで位置情報付きの提案を取得し、自動マッピングする。

> **前提**: 対象ファイルが単体でコンパイル可能な状態であること（`lake build` でエラー 0）。

### 概要

```
1. bare simp → simp?/simp_all? に一括変換（テキスト置換）
2. `lake env lean --json <file>` で位置付き提案を取得
3. JSON パース → 行番号でマッピング → ソースに適用
4. `lake build` で検証
5. unused simp argument 警告の除去
```

### Step 1: simp → simp? への一括変換

対象ファイルをバックアップ後、以下のパターンで変換する:

**推奨**: 下表の 4 カテゴリを最初にまとめて `simp?` / `simp_all?` 化し、`lean --json` は **1 回だけ** 実行する。
`simp [X]` だけ先に処理し、あとから bare `simp` / `simp_all` を追加で処理すると、同じファイルに対して
`lean --json` を複数回回すことになり、セッション時間を無駄にしやすい。

| 変換前 | 変換後 | 備考 |
|---|---|---|
| `simp only [...]` | （変換しない） | 既に安定化済み |
| `simp_all only [...]` | （変換しない） | 既に安定化済み |
| `simp [...]` | `simp? [...]` | |
| `simp_all [...]` | `simp_all? [...]` | |
| `simp` (引数なし) | `simp?` | |
| `simp_all` (引数なし) | `simp_all?` | |
| `<;> simp` | `<;> simp?` | チェーン行 |

**注意**: `simp_all (config := ...) only [...]` のような既に安定化済みの形式を誤変換しないこと。

処理対象のチェックリスト:

| カテゴリ | 典型例 | 先に一括変換するか |
|---|---|---|
| `simp [X]` | `simp [List.getD]` | ✓ |
| `simp_all [X]` | `simp_all [Quarter.isEmpty]` | ✓ |
| bare `simp` | `simp at h`, `by simp`, `<;> simp` | ✓ |
| bare `simp_all` | `cases q <;> simp_all` | ✓ |

### Step 2: lean --json で提案取得

```powershell
# .NET ProcessStartInfo を使用（PowerShell のパイプは UTF-8 文字を化かすため）
$psi = New-Object System.Diagnostics.ProcessStartInfo
$psi.FileName = "lake"
$psi.Arguments = "env lean --json <file>"
$psi.RedirectStandardOutput = $true
$psi.RedirectStandardError = $true
$psi.UseShellExecute = $false
$psi.StandardOutputEncoding = [System.Text.Encoding]::UTF8
$p = [System.Diagnostics.Process]::Start($psi)
$stdout = $p.StandardOutput.ReadToEnd()
$p.WaitForExit()
# BOM なし UTF-8 で書き出し
[System.IO.File]::WriteAllText("output.jsonl", $stdout,
    (New-Object System.Text.UTF8Encoding $false))
```

> **重要**: `Set-Content` や PowerShell パイプ (`|`) は Unicode 文字（`↓reduceIte` 等）を
> 壊すため、必ず `.NET ProcessStartInfo` + `StandardOutputEncoding = UTF8` を使用する。

各行が以下の形式の JSON:
```json
{"severity":"info","pos":{"line":42,"column":4},"data":"Try this:\n  simp only [add_zero, mul_one]"}
```

- `pos.line` / `pos.column`: ソース中の位置（1-based）
- `data`: `Try this:` から始まる提案テキスト

### Step 3: JSON パース → マッピング → 適用

```
1. severity="info" かつ data に "Try this:" を含むメッセージを抽出
2. pos.line でグループ化（チェーン行は同一行で複数提案）
3. 提案テキストから simp only [...] を抽出
4. チェーン行（<;> simp?）: 複数提案の補題リストを和集合でマージ
5. at ターゲットのマッチ: \w[\w'_]* を使用（\S+ は ) 等を飲み込む）
6. ソースファイルの該当行を置換
```

**正規表現の注意点**:
- simp? の提案は**複数行**にまたがることがある → `(?s)` フラグを使用
- `at target` パターン: `\w[\w'_]*` でマッチ（`\S+` は `)` 等の区切り文字を消費する）
- ネスト括弧（`simp [show (expr) from by tactic]`）は正規表現で処理不可 → 手動修正

### Step 4: ビルド検証

```powershell
.github/skills/lean-build/scripts/build.ps1
```

### Step 5: unused argument 警告の除去

ビルド出力に `This simp argument is unused:` 警告が出る場合、該当引数を削除する。

**注意**: 削除前に REPL またはビルドで検証すること。Explore サブエージェントのコードリーディングだけでは
意味論的な依存関係が分からず、必要な引数を誤って削除するリスクがある。

### 永続化スクリプト

`.github/skills/lean-simp-guide/scripts/` に以下のスクリプトが利用可能:

| スクリプト | 用途 |
|---|---|
| `simp-stabilize.ps1` | bare simp → simp? 変換 + lean --json 実行 + 提案適用の一括パイプライン (Windows) |
| `simp-stabilize.sh` | 同上 (macOS / Linux、python3 または jq が必要) |

使い方:
```powershell
# Windows
.github/skills/lean-simp-guide/scripts/simp-stabilize.ps1 -File S2IL/Behavior/Gravity.lean
.github/skills/lean-simp-guide/scripts/simp-stabilize.ps1 -File S2IL/Behavior/Gravity.lean -DryRun
.github/skills/lean-simp-guide/scripts/simp-stabilize.ps1 -File S2IL/Behavior/Gravity.lean -KeepBackup
```
```bash
# macOS / Linux
.github/skills/lean-simp-guide/scripts/simp-stabilize.sh --file S2IL/Behavior/Gravity.lean
.github/skills/lean-simp-guide/scripts/simp-stabilize.sh --file S2IL/Behavior/Gravity.lean --dry-run
.github/skills/lean-simp-guide/scripts/simp-stabilize.sh --file S2IL/Behavior/Gravity.lean --keep-backup
```

---

## 関連

- **lean-tactic-select** — ゴール形状からタクティクを選択
- **lean-simp-stabilizer** エージェント — simp → simp only の自動安定化（単一行・バルク両対応）
